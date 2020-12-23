%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:53 EST 2020

% Result     : Theorem 3.73s
% Output     : Refutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :  297 (4002 expanded)
%              Number of leaves         :   13 ( 759 expanded)
%              Depth                    :   38
%              Number of atoms          : 1077 (30207 expanded)
%              Number of equality atoms :   74 ( 407 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4747,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4746,f88])).

fof(f88,plain,(
    l1_pre_topc(sK3) ),
    inference(resolution,[],[f87,f39])).

fof(f39,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

fof(f87,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f62,f47])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f4746,plain,(
    ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f4708,f51])).

fof(f51,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f4708,plain,(
    ~ l1_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f1587,f4697])).

fof(f4697,plain,(
    r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) ),
    inference(resolution,[],[f4586,f3136])).

fof(f3136,plain,(
    r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f3135,f2560])).

fof(f2560,plain,(
    l1_pre_topc(k1_tsep_1(sK0,sK2,sK2)) ),
    inference(subsumption_resolution,[],[f2559,f42])).

fof(f42,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f2559,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | l1_pre_topc(k1_tsep_1(sK0,sK2,sK2)) ),
    inference(subsumption_resolution,[],[f2547,f41])).

fof(f41,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f2547,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | l1_pre_topc(k1_tsep_1(sK0,sK2,sK2)) ),
    inference(duplicate_literal_removal,[],[f2536])).

fof(f2536,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | l1_pre_topc(k1_tsep_1(sK0,sK2,sK2)) ),
    inference(resolution,[],[f642,f1711])).

fof(f1711,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,k1_tsep_1(sK0,sK2,sK2))
      | l1_pre_topc(X4) ) ),
    inference(subsumption_resolution,[],[f1708,f41])).

fof(f1708,plain,(
    ! [X4] :
      ( v2_struct_0(sK2)
      | ~ m1_pre_topc(X4,k1_tsep_1(sK0,sK2,sK2))
      | l1_pre_topc(X4) ) ),
    inference(resolution,[],[f1658,f42])).

fof(f1658,plain,(
    ! [X6,X7] :
      ( ~ m1_pre_topc(X6,sK0)
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X7,k1_tsep_1(sK0,sK2,X6))
      | l1_pre_topc(X7) ) ),
    inference(subsumption_resolution,[],[f1655,f41])).

fof(f1655,plain,(
    ! [X6,X7] :
      ( ~ m1_pre_topc(X6,sK0)
      | v2_struct_0(sK2)
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X7,k1_tsep_1(sK0,sK2,X6))
      | l1_pre_topc(X7) ) ),
    inference(resolution,[],[f645,f42])).

fof(f645,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,k1_tsep_1(sK0,X1,X0))
      | l1_pre_topc(X2) ) ),
    inference(resolution,[],[f644,f62])).

fof(f644,plain,(
    ! [X4,X5] :
      ( l1_pre_topc(k1_tsep_1(sK0,X4,X5))
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,sK0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,sK0) ) ),
    inference(resolution,[],[f638,f87])).

fof(f638,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f634,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f634,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,sK0)
      | m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0) ) ),
    inference(resolution,[],[f78,f47])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f642,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tsep_1(sK0,X0,X1),k1_tsep_1(sK0,X0,X1))
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f638,f322])).

fof(f322,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_pre_topc(X0,X0) ) ),
    inference(subsumption_resolution,[],[f318,f46])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f318,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_pre_topc(X0,X0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f314,f47])).

fof(f314,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(X1,X1)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f305])).

fof(f305,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(X1,X1)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f68,f81])).

fof(f81,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X1,X2)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f3135,plain,
    ( r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2))
    | ~ l1_pre_topc(k1_tsep_1(sK0,sK2,sK2)) ),
    inference(resolution,[],[f3116,f51])).

fof(f3116,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK0,sK2,sK2))
    | r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f2070,f3114])).

fof(f3114,plain,(
    r1_tsep_1(sK3,k1_tsep_1(sK0,sK2,sK2)) ),
    inference(subsumption_resolution,[],[f3113,f2560])).

fof(f3113,plain,
    ( r1_tsep_1(sK3,k1_tsep_1(sK0,sK2,sK2))
    | ~ l1_pre_topc(k1_tsep_1(sK0,sK2,sK2)) ),
    inference(subsumption_resolution,[],[f3112,f122])).

fof(f122,plain,(
    r1_tsep_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f121,f90])).

fof(f90,plain,(
    l1_pre_topc(sK2) ),
    inference(resolution,[],[f87,f42])).

fof(f121,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f117,f120])).

fof(f120,plain,(
    r1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f119,f88])).

fof(f119,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | r1_tsep_1(sK2,sK3) ),
    inference(resolution,[],[f116,f36])).

fof(f36,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f116,plain,(
    ! [X2] :
      ( ~ r1_tsep_1(X2,sK2)
      | r1_tsep_1(sK2,X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f113,f90])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f112,f51])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f69,f51])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f117,plain,(
    ! [X3] :
      ( ~ r1_tsep_1(X3,sK3)
      | r1_tsep_1(sK3,X3)
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f113,f88])).

fof(f3112,plain,
    ( ~ r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK3,k1_tsep_1(sK0,sK2,sK2))
    | ~ l1_pre_topc(k1_tsep_1(sK0,sK2,sK2)) ),
    inference(subsumption_resolution,[],[f3086,f88])).

fof(f3086,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK3,k1_tsep_1(sK0,sK2,sK2))
    | ~ l1_pre_topc(k1_tsep_1(sK0,sK2,sK2)) ),
    inference(resolution,[],[f3054,f117])).

fof(f3054,plain,(
    ! [X0] :
      ( r1_tsep_1(k1_tsep_1(sK0,sK2,sK2),X0)
      | ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f3044,f51])).

fof(f3044,plain,(
    ! [X0] :
      ( r1_tsep_1(k1_tsep_1(sK0,sK2,sK2),X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,sK2) ) ),
    inference(resolution,[],[f2597,f2357])).

fof(f2357,plain,(
    ! [X0] :
      ( r1_tsep_1(X0,k1_tsep_1(sK0,sK2,sK2))
      | ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,sK2) ) ),
    inference(duplicate_literal_removal,[],[f2348])).

fof(f2348,plain,(
    ! [X0] :
      ( r1_tsep_1(X0,k1_tsep_1(sK0,sK2,sK2))
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,sK2) ) ),
    inference(resolution,[],[f2347,f340])).

fof(f340,plain,(
    ! [X0] :
      ( r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK2))
      | ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f339,f90])).

fof(f339,plain,(
    ! [X0] :
      ( r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK2))
      | ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,sK2)
      | ~ l1_pre_topc(sK2) ) ),
    inference(resolution,[],[f143,f51])).

fof(f143,plain,(
    ! [X2] :
      ( ~ l1_struct_0(sK2)
      | r1_xboole_0(u1_struct_0(X2),k2_struct_0(sK2))
      | ~ l1_struct_0(X2)
      | ~ r1_tsep_1(X2,sK2) ) ),
    inference(superposition,[],[f50,f97])).

fof(f97,plain,(
    k2_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(resolution,[],[f86,f90])).

fof(f86,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f48,f51])).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f2347,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK2))
      | r1_tsep_1(X0,k1_tsep_1(sK0,sK2,sK2))
      | ~ l1_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f2346,f42])).

fof(f2346,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | r1_tsep_1(X0,k1_tsep_1(sK0,sK2,sK2))
      | ~ r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK2))
      | ~ m1_pre_topc(sK2,sK0) ) ),
    inference(subsumption_resolution,[],[f2345,f41])).

fof(f2345,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | r1_tsep_1(X0,k1_tsep_1(sK0,sK2,sK2))
      | ~ r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK2))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0) ) ),
    inference(duplicate_literal_removal,[],[f2344])).

fof(f2344,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | r1_tsep_1(X0,k1_tsep_1(sK0,sK2,sK2))
      | ~ r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK2))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0) ) ),
    inference(resolution,[],[f2242,f644])).

fof(f2242,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(k1_tsep_1(sK0,sK2,sK2))
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X0,k1_tsep_1(sK0,sK2,sK2))
      | ~ r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK2)) ) ),
    inference(resolution,[],[f2072,f51])).

fof(f2072,plain,(
    ! [X1] :
      ( ~ l1_struct_0(k1_tsep_1(sK0,sK2,sK2))
      | ~ r1_xboole_0(u1_struct_0(X1),k2_struct_0(sK2))
      | ~ l1_struct_0(X1)
      | r1_tsep_1(X1,k1_tsep_1(sK0,sK2,sK2)) ) ),
    inference(resolution,[],[f2052,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2052,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,u1_struct_0(k1_tsep_1(sK0,sK2,sK2)))
      | ~ r1_xboole_0(X0,k2_struct_0(sK2)) ) ),
    inference(duplicate_literal_removal,[],[f2049])).

fof(f2049,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,u1_struct_0(k1_tsep_1(sK0,sK2,sK2)))
      | ~ r1_xboole_0(X0,k2_struct_0(sK2))
      | ~ r1_xboole_0(X0,k2_struct_0(sK2)) ) ),
    inference(superposition,[],[f75,f2043])).

fof(f2043,plain,(
    u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) = k2_xboole_0(k2_struct_0(sK2),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f2042,f97])).

fof(f2042,plain,(
    u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) = k2_xboole_0(u1_struct_0(sK2),k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f2038,f41])).

fof(f2038,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) = k2_xboole_0(u1_struct_0(sK2),k2_struct_0(sK2))
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f1966,f42])).

fof(f1966,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK0)
      | k2_xboole_0(u1_struct_0(X4),k2_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,X4,sK2))
      | v2_struct_0(X4) ) ),
    inference(forward_demodulation,[],[f1965,f97])).

fof(f1965,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK0)
      | v2_struct_0(X4)
      | k2_xboole_0(u1_struct_0(X4),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,X4,sK2)) ) ),
    inference(subsumption_resolution,[],[f1961,f41])).

fof(f1961,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK0)
      | v2_struct_0(sK2)
      | v2_struct_0(X4)
      | k2_xboole_0(u1_struct_0(X4),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,X4,sK2)) ) ),
    inference(resolution,[],[f1336,f42])).

fof(f1336,plain,(
    ! [X17,X16] :
      ( ~ m1_pre_topc(X17,sK0)
      | ~ m1_pre_topc(X16,sK0)
      | v2_struct_0(X17)
      | v2_struct_0(X16)
      | k2_xboole_0(u1_struct_0(X16),u1_struct_0(X17)) = u1_struct_0(k1_tsep_1(sK0,X16,X17)) ) ),
    inference(subsumption_resolution,[],[f1332,f45])).

fof(f1332,plain,(
    ! [X17,X16] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,sK0)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,sK0)
      | k2_xboole_0(u1_struct_0(X16),u1_struct_0(X17)) = u1_struct_0(k1_tsep_1(sK0,X16,X17)) ) ),
    inference(resolution,[],[f85,f47])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f84,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f83,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f80,f78])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ v1_pre_topc(X3)
      | ~ m1_pre_topc(X3,X0)
      | u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k1_tsep_1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                 => ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f2597,plain,(
    ! [X12] :
      ( ~ r1_tsep_1(X12,k1_tsep_1(sK0,sK2,sK2))
      | r1_tsep_1(k1_tsep_1(sK0,sK2,sK2),X12)
      | ~ l1_pre_topc(X12) ) ),
    inference(resolution,[],[f2560,f113])).

fof(f2070,plain,
    ( ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK2,sK2))
    | ~ l1_struct_0(k1_tsep_1(sK0,sK2,sK2))
    | r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(resolution,[],[f2050,f275])).

fof(f275,plain,(
    ! [X0] :
      ( r1_xboole_0(k2_struct_0(sK3),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ r1_tsep_1(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f274,f88])).

fof(f274,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | r1_xboole_0(k2_struct_0(sK3),u1_struct_0(X0))
      | ~ r1_tsep_1(sK3,X0)
      | ~ l1_pre_topc(sK3) ) ),
    inference(resolution,[],[f140,f51])).

fof(f140,plain,(
    ! [X3] :
      ( ~ l1_struct_0(sK3)
      | ~ l1_struct_0(X3)
      | r1_xboole_0(k2_struct_0(sK3),u1_struct_0(X3))
      | ~ r1_tsep_1(sK3,X3) ) ),
    inference(superposition,[],[f50,f98])).

fof(f98,plain,(
    k2_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(resolution,[],[f86,f88])).

fof(f2050,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,u1_struct_0(k1_tsep_1(sK0,sK2,sK2)))
      | r1_xboole_0(X1,k2_struct_0(sK2)) ) ),
    inference(superposition,[],[f74,f2043])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4586,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,k2_struct_0(sK2))
      | r1_xboole_0(X1,k2_struct_0(sK1)) ) ),
    inference(backward_demodulation,[],[f3778,f4583])).

fof(f4583,plain,(
    k2_struct_0(sK2) = k2_struct_0(k1_tsep_1(sK0,sK2,sK1)) ),
    inference(forward_demodulation,[],[f4582,f989])).

fof(f989,plain,(
    k2_struct_0(sK2) = u1_struct_0(k1_tsep_1(sK2,sK2,sK1)) ),
    inference(subsumption_resolution,[],[f988,f41])).

fof(f988,plain,
    ( k2_struct_0(sK2) = u1_struct_0(k1_tsep_1(sK2,sK2,sK1))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f987,f40])).

fof(f40,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f987,plain,
    ( k2_struct_0(sK2) = u1_struct_0(k1_tsep_1(sK2,sK2,sK1))
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f986,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f986,plain,
    ( k2_struct_0(sK2) = u1_struct_0(k1_tsep_1(sK2,sK2,sK1))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f985,f328])).

fof(f328,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f322,f42])).

fof(f985,plain,
    ( k2_struct_0(sK2) = u1_struct_0(k1_tsep_1(sK2,sK2,sK1))
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f937,f640])).

fof(f640,plain,(
    ! [X4,X5] :
      ( m1_pre_topc(k1_tsep_1(sK2,X4,X5),sK2)
      | ~ m1_pre_topc(X4,sK2)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,sK2)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f636,f41])).

fof(f636,plain,(
    ! [X4,X5] :
      ( v2_struct_0(sK2)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,sK2)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,sK2)
      | m1_pre_topc(k1_tsep_1(sK2,X4,X5),sK2) ) ),
    inference(resolution,[],[f78,f90])).

fof(f937,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK2,sK1),sK2)
    | k2_struct_0(sK2) = u1_struct_0(k1_tsep_1(sK2,sK2,sK1)) ),
    inference(resolution,[],[f933,f564])).

fof(f564,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(X0,sK2)
      | u1_struct_0(X0) = k2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f558,f543])).

fof(f543,plain,(
    ! [X2] :
      ( r1_tarski(u1_struct_0(X2),k2_struct_0(sK2))
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(subsumption_resolution,[],[f540,f328])).

fof(f540,plain,(
    ! [X2] :
      ( r1_tarski(u1_struct_0(X2),k2_struct_0(sK2))
      | ~ m1_pre_topc(sK2,sK2)
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(duplicate_literal_removal,[],[f538])).

fof(f538,plain,(
    ! [X2] :
      ( r1_tarski(u1_struct_0(X2),k2_struct_0(sK2))
      | ~ m1_pre_topc(sK2,sK2)
      | ~ m1_pre_topc(X2,sK2)
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(superposition,[],[f235,f97])).

fof(f235,plain,(
    ! [X4,X5] :
      ( r1_tarski(u1_struct_0(X4),u1_struct_0(X5))
      | ~ m1_pre_topc(X5,sK2)
      | ~ m1_pre_topc(X4,X5)
      | ~ m1_pre_topc(X4,sK2) ) ),
    inference(subsumption_resolution,[],[f231,f106])).

fof(f106,plain,(
    v2_pre_topc(sK2) ),
    inference(resolution,[],[f103,f42])).

fof(f103,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f99,f46])).

fof(f99,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_pre_topc(X0) ) ),
    inference(resolution,[],[f66,f47])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f231,plain,(
    ! [X4,X5] :
      ( ~ v2_pre_topc(sK2)
      | ~ m1_pre_topc(X4,sK2)
      | ~ m1_pre_topc(X5,sK2)
      | ~ m1_pre_topc(X4,X5)
      | r1_tarski(u1_struct_0(X4),u1_struct_0(X5)) ) ),
    inference(resolution,[],[f67,f90])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f558,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(sK2,X0)
      | ~ r1_tarski(u1_struct_0(X0),k2_struct_0(sK2))
      | u1_struct_0(X0) = k2_struct_0(sK2) ) ),
    inference(resolution,[],[f542,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f542,plain,(
    ! [X2] :
      ( r1_tarski(k2_struct_0(sK2),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,sK2)
      | ~ m1_pre_topc(sK2,X2) ) ),
    inference(subsumption_resolution,[],[f534,f328])).

fof(f534,plain,(
    ! [X2] :
      ( r1_tarski(k2_struct_0(sK2),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,sK2)
      | ~ m1_pre_topc(sK2,X2)
      | ~ m1_pre_topc(sK2,sK2) ) ),
    inference(superposition,[],[f235,f97])).

fof(f933,plain,(
    m1_pre_topc(sK2,k1_tsep_1(sK2,sK2,sK1)) ),
    inference(subsumption_resolution,[],[f931,f41])).

fof(f931,plain,
    ( v2_struct_0(sK2)
    | m1_pre_topc(sK2,k1_tsep_1(sK2,sK2,sK1)) ),
    inference(resolution,[],[f927,f328])).

fof(f927,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3)
      | m1_pre_topc(X3,k1_tsep_1(sK2,X3,sK1)) ) ),
    inference(subsumption_resolution,[],[f925,f43])).

fof(f925,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(sK1)
      | v2_struct_0(X3)
      | m1_pre_topc(X3,k1_tsep_1(sK2,X3,sK1)) ) ),
    inference(resolution,[],[f792,f40])).

fof(f792,plain,(
    ! [X21,X20] :
      ( ~ m1_pre_topc(X21,sK2)
      | ~ m1_pre_topc(X20,sK2)
      | v2_struct_0(X21)
      | v2_struct_0(X20)
      | m1_pre_topc(X20,k1_tsep_1(sK2,X20,X21)) ) ),
    inference(subsumption_resolution,[],[f791,f41])).

fof(f791,plain,(
    ! [X21,X20] :
      ( v2_struct_0(sK2)
      | v2_struct_0(X20)
      | ~ m1_pre_topc(X20,sK2)
      | v2_struct_0(X21)
      | ~ m1_pre_topc(X21,sK2)
      | m1_pre_topc(X20,k1_tsep_1(sK2,X20,X21)) ) ),
    inference(subsumption_resolution,[],[f781,f106])).

fof(f781,plain,(
    ! [X21,X20] :
      ( ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | v2_struct_0(X20)
      | ~ m1_pre_topc(X20,sK2)
      | v2_struct_0(X21)
      | ~ m1_pre_topc(X21,sK2)
      | m1_pre_topc(X20,k1_tsep_1(sK2,X20,X21)) ) ),
    inference(resolution,[],[f63,f90])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
             => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tsep_1)).

fof(f4582,plain,(
    k2_struct_0(k1_tsep_1(sK0,sK2,sK1)) = u1_struct_0(k1_tsep_1(sK2,sK2,sK1)) ),
    inference(forward_demodulation,[],[f4581,f3780])).

fof(f3780,plain,(
    k2_struct_0(k1_tsep_1(sK0,sK2,sK1)) = k2_xboole_0(k2_struct_0(sK2),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f1978,f3776])).

fof(f3776,plain,(
    k2_struct_0(k1_tsep_1(sK0,sK2,sK1)) = u1_struct_0(k1_tsep_1(sK0,sK2,sK1)) ),
    inference(subsumption_resolution,[],[f3773,f43])).

fof(f3773,plain,
    ( v2_struct_0(sK1)
    | k2_struct_0(k1_tsep_1(sK0,sK2,sK1)) = u1_struct_0(k1_tsep_1(sK0,sK2,sK1)) ),
    inference(resolution,[],[f3183,f44])).

fof(f44,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f3183,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK0)
      | v2_struct_0(X4)
      | k2_struct_0(k1_tsep_1(sK0,sK2,X4)) = u1_struct_0(k1_tsep_1(sK0,sK2,X4)) ) ),
    inference(subsumption_resolution,[],[f3180,f41])).

fof(f3180,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK0)
      | v2_struct_0(sK2)
      | v2_struct_0(X4)
      | k2_struct_0(k1_tsep_1(sK0,sK2,X4)) = u1_struct_0(k1_tsep_1(sK0,sK2,X4)) ) ),
    inference(resolution,[],[f649,f42])).

fof(f649,plain,(
    ! [X14,X15] :
      ( ~ m1_pre_topc(X15,sK0)
      | ~ m1_pre_topc(X14,sK0)
      | v2_struct_0(X15)
      | v2_struct_0(X14)
      | k2_struct_0(k1_tsep_1(sK0,X15,X14)) = u1_struct_0(k1_tsep_1(sK0,X15,X14)) ) ),
    inference(resolution,[],[f644,f86])).

fof(f1978,plain,(
    u1_struct_0(k1_tsep_1(sK0,sK2,sK1)) = k2_xboole_0(k2_struct_0(sK2),k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f1977,f97])).

fof(f1977,plain,(
    u1_struct_0(k1_tsep_1(sK0,sK2,sK1)) = k2_xboole_0(u1_struct_0(sK2),k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f1973,f41])).

fof(f1973,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK1)) = k2_xboole_0(u1_struct_0(sK2),k2_struct_0(sK1))
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f1964,f42])).

fof(f1964,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK0)
      | u1_struct_0(k1_tsep_1(sK0,X3,sK1)) = k2_xboole_0(u1_struct_0(X3),k2_struct_0(sK1))
      | v2_struct_0(X3) ) ),
    inference(forward_demodulation,[],[f1963,f96])).

fof(f96,plain,(
    k2_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(resolution,[],[f86,f89])).

fof(f89,plain,(
    l1_pre_topc(sK1) ),
    inference(resolution,[],[f87,f44])).

fof(f1963,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK0)
      | v2_struct_0(X3)
      | k2_xboole_0(u1_struct_0(X3),u1_struct_0(sK1)) = u1_struct_0(k1_tsep_1(sK0,X3,sK1)) ) ),
    inference(subsumption_resolution,[],[f1960,f43])).

fof(f1960,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(X3)
      | k2_xboole_0(u1_struct_0(X3),u1_struct_0(sK1)) = u1_struct_0(k1_tsep_1(sK0,X3,sK1)) ) ),
    inference(resolution,[],[f1336,f44])).

fof(f4581,plain,(
    u1_struct_0(k1_tsep_1(sK2,sK2,sK1)) = k2_xboole_0(k2_struct_0(sK2),k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f4580,f97])).

fof(f4580,plain,(
    u1_struct_0(k1_tsep_1(sK2,sK2,sK1)) = k2_xboole_0(u1_struct_0(sK2),k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f4576,f41])).

fof(f4576,plain,
    ( u1_struct_0(k1_tsep_1(sK2,sK2,sK1)) = k2_xboole_0(u1_struct_0(sK2),k2_struct_0(sK1))
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f3446,f328])).

fof(f3446,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK2)
      | k2_xboole_0(u1_struct_0(X3),k2_struct_0(sK1)) = u1_struct_0(k1_tsep_1(sK2,X3,sK1))
      | v2_struct_0(X3) ) ),
    inference(forward_demodulation,[],[f3445,f96])).

fof(f3445,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3)
      | k2_xboole_0(u1_struct_0(X3),u1_struct_0(sK1)) = u1_struct_0(k1_tsep_1(sK2,X3,sK1)) ) ),
    inference(subsumption_resolution,[],[f3443,f43])).

fof(f3443,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(sK1)
      | v2_struct_0(X3)
      | k2_xboole_0(u1_struct_0(X3),u1_struct_0(sK1)) = u1_struct_0(k1_tsep_1(sK2,X3,sK1)) ) ),
    inference(resolution,[],[f1338,f40])).

fof(f1338,plain,(
    ! [X21,X20] :
      ( ~ m1_pre_topc(X21,sK2)
      | ~ m1_pre_topc(X20,sK2)
      | v2_struct_0(X21)
      | v2_struct_0(X20)
      | k2_xboole_0(u1_struct_0(X20),u1_struct_0(X21)) = u1_struct_0(k1_tsep_1(sK2,X20,X21)) ) ),
    inference(subsumption_resolution,[],[f1334,f41])).

fof(f1334,plain,(
    ! [X21,X20] :
      ( v2_struct_0(sK2)
      | v2_struct_0(X20)
      | ~ m1_pre_topc(X20,sK2)
      | v2_struct_0(X21)
      | ~ m1_pre_topc(X21,sK2)
      | k2_xboole_0(u1_struct_0(X20),u1_struct_0(X21)) = u1_struct_0(k1_tsep_1(sK2,X20,X21)) ) ),
    inference(resolution,[],[f85,f90])).

fof(f3778,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,k2_struct_0(k1_tsep_1(sK0,sK2,sK1)))
      | r1_xboole_0(X1,k2_struct_0(sK1)) ) ),
    inference(backward_demodulation,[],[f1986,f3776])).

fof(f1986,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,u1_struct_0(k1_tsep_1(sK0,sK2,sK1)))
      | r1_xboole_0(X1,k2_struct_0(sK1)) ) ),
    inference(superposition,[],[f74,f1978])).

fof(f1587,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))
    | ~ l1_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f214,f1585])).

fof(f1585,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ l1_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f1583,f1477])).

fof(f1477,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3))
    | ~ l1_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f191,f1476])).

fof(f1476,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | ~ l1_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f1475,f37])).

fof(f37,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f1475,plain,
    ( ~ l1_struct_0(sK3)
    | r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(duplicate_literal_removal,[],[f1474])).

fof(f1474,plain,
    ( ~ l1_struct_0(sK3)
    | r1_tsep_1(sK3,sK1)
    | ~ l1_struct_0(sK3)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(resolution,[],[f1471,f244])).

fof(f244,plain,
    ( r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3))
    | ~ l1_struct_0(sK3)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(superposition,[],[f239,f98])).

fof(f239,plain,(
    ! [X0] :
      ( r1_xboole_0(k2_struct_0(sK1),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ r1_tsep_1(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f238,f89])).

fof(f238,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | r1_xboole_0(k2_struct_0(sK1),u1_struct_0(X0))
      | ~ r1_tsep_1(sK1,X0)
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f138,f51])).

fof(f138,plain,(
    ! [X1] :
      ( ~ l1_struct_0(sK1)
      | ~ l1_struct_0(X1)
      | r1_xboole_0(k2_struct_0(sK1),u1_struct_0(X1))
      | ~ r1_tsep_1(sK1,X1) ) ),
    inference(superposition,[],[f50,f96])).

fof(f1471,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3))
    | ~ l1_struct_0(sK3)
    | r1_tsep_1(sK3,sK1) ),
    inference(resolution,[],[f1470,f214])).

fof(f1470,plain,
    ( r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))
    | ~ r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f1469,f327])).

fof(f327,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(resolution,[],[f322,f44])).

fof(f1469,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3))
    | r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK1) ),
    inference(subsumption_resolution,[],[f1468,f43])).

fof(f1468,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3))
    | r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK1) ),
    inference(duplicate_literal_removal,[],[f1467])).

fof(f1467,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3))
    | r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK1) ),
    inference(resolution,[],[f1466,f657])).

fof(f657,plain,(
    ! [X4,X5] :
      ( l1_pre_topc(k1_tsep_1(sK1,X4,X5))
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,sK1)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,sK1) ) ),
    inference(resolution,[],[f639,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f89,f62])).

fof(f639,plain,(
    ! [X2,X3] :
      ( m1_pre_topc(k1_tsep_1(sK1,X2,X3),sK1)
      | ~ m1_pre_topc(X2,sK1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,sK1)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f635,f43])).

fof(f635,plain,(
    ! [X2,X3] :
      ( v2_struct_0(sK1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,sK1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,sK1)
      | m1_pre_topc(k1_tsep_1(sK1,X2,X3),sK1) ) ),
    inference(resolution,[],[f78,f89])).

fof(f1466,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK1,sK1,sK1))
    | ~ r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3))
    | r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f1465,f51])).

fof(f1465,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3))
    | ~ l1_pre_topc(k1_tsep_1(sK1,sK1,sK1))
    | ~ l1_struct_0(k1_tsep_1(sK1,sK1,sK1))
    | r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) ),
    inference(resolution,[],[f1245,f894])).

fof(f894,plain,
    ( ~ r1_tsep_1(sK3,k1_tsep_1(sK1,sK1,sK1))
    | ~ l1_struct_0(k1_tsep_1(sK1,sK1,sK1))
    | r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) ),
    inference(superposition,[],[f275,f866])).

fof(f866,plain,(
    k2_struct_0(sK1) = u1_struct_0(k1_tsep_1(sK1,sK1,sK1)) ),
    inference(subsumption_resolution,[],[f865,f43])).

fof(f865,plain,
    ( k2_struct_0(sK1) = u1_struct_0(k1_tsep_1(sK1,sK1,sK1))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f864,f327])).

fof(f864,plain,
    ( k2_struct_0(sK1) = u1_struct_0(k1_tsep_1(sK1,sK1,sK1))
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1) ),
    inference(duplicate_literal_removal,[],[f863])).

fof(f863,plain,
    ( k2_struct_0(sK1) = u1_struct_0(k1_tsep_1(sK1,sK1,sK1))
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f848,f639])).

fof(f848,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK1,sK1,sK1),sK1)
    | k2_struct_0(sK1) = u1_struct_0(k1_tsep_1(sK1,sK1,sK1)) ),
    inference(resolution,[],[f846,f513])).

fof(f513,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK1,X0)
      | ~ m1_pre_topc(X0,sK1)
      | u1_struct_0(X0) = k2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f507,f501])).

fof(f501,plain,(
    ! [X1] :
      ( r1_tarski(u1_struct_0(X1),k2_struct_0(sK1))
      | ~ m1_pre_topc(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f499,f327])).

fof(f499,plain,(
    ! [X1] :
      ( r1_tarski(u1_struct_0(X1),k2_struct_0(sK1))
      | ~ m1_pre_topc(sK1,sK1)
      | ~ m1_pre_topc(X1,sK1) ) ),
    inference(duplicate_literal_removal,[],[f496])).

fof(f496,plain,(
    ! [X1] :
      ( r1_tarski(u1_struct_0(X1),k2_struct_0(sK1))
      | ~ m1_pre_topc(sK1,sK1)
      | ~ m1_pre_topc(X1,sK1)
      | ~ m1_pre_topc(X1,sK1) ) ),
    inference(superposition,[],[f234,f96])).

fof(f234,plain,(
    ! [X2,X3] :
      ( r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
      | ~ m1_pre_topc(X3,sK1)
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_pre_topc(X2,sK1) ) ),
    inference(subsumption_resolution,[],[f230,f105])).

fof(f105,plain,(
    v2_pre_topc(sK1) ),
    inference(resolution,[],[f103,f44])).

fof(f230,plain,(
    ! [X2,X3] :
      ( ~ v2_pre_topc(sK1)
      | ~ m1_pre_topc(X2,sK1)
      | ~ m1_pre_topc(X3,sK1)
      | ~ m1_pre_topc(X2,X3)
      | r1_tarski(u1_struct_0(X2),u1_struct_0(X3)) ) ),
    inference(resolution,[],[f67,f89])).

fof(f507,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | ~ m1_pre_topc(sK1,X0)
      | ~ r1_tarski(u1_struct_0(X0),k2_struct_0(sK1))
      | u1_struct_0(X0) = k2_struct_0(sK1) ) ),
    inference(resolution,[],[f500,f72])).

fof(f500,plain,(
    ! [X1] :
      ( r1_tarski(k2_struct_0(sK1),u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK1)
      | ~ m1_pre_topc(sK1,X1) ) ),
    inference(subsumption_resolution,[],[f492,f327])).

fof(f492,plain,(
    ! [X1] :
      ( r1_tarski(k2_struct_0(sK1),u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK1)
      | ~ m1_pre_topc(sK1,X1)
      | ~ m1_pre_topc(sK1,sK1) ) ),
    inference(superposition,[],[f234,f96])).

fof(f846,plain,(
    m1_pre_topc(sK1,k1_tsep_1(sK1,sK1,sK1)) ),
    inference(subsumption_resolution,[],[f845,f43])).

fof(f845,plain,
    ( v2_struct_0(sK1)
    | m1_pre_topc(sK1,k1_tsep_1(sK1,sK1,sK1)) ),
    inference(resolution,[],[f843,f327])).

fof(f843,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK1)
      | v2_struct_0(X3)
      | m1_pre_topc(X3,k1_tsep_1(sK1,X3,sK1)) ) ),
    inference(subsumption_resolution,[],[f842,f43])).

fof(f842,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK1)
      | v2_struct_0(sK1)
      | v2_struct_0(X3)
      | m1_pre_topc(X3,k1_tsep_1(sK1,X3,sK1)) ) ),
    inference(resolution,[],[f790,f327])).

fof(f790,plain,(
    ! [X19,X18] :
      ( ~ m1_pre_topc(X19,sK1)
      | ~ m1_pre_topc(X18,sK1)
      | v2_struct_0(X19)
      | v2_struct_0(X18)
      | m1_pre_topc(X18,k1_tsep_1(sK1,X18,X19)) ) ),
    inference(subsumption_resolution,[],[f789,f43])).

fof(f789,plain,(
    ! [X19,X18] :
      ( v2_struct_0(sK1)
      | v2_struct_0(X18)
      | ~ m1_pre_topc(X18,sK1)
      | v2_struct_0(X19)
      | ~ m1_pre_topc(X19,sK1)
      | m1_pre_topc(X18,k1_tsep_1(sK1,X18,X19)) ) ),
    inference(subsumption_resolution,[],[f780,f105])).

fof(f780,plain,(
    ! [X19,X18] :
      ( ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | v2_struct_0(X18)
      | ~ m1_pre_topc(X18,sK1)
      | v2_struct_0(X19)
      | ~ m1_pre_topc(X19,sK1)
      | m1_pre_topc(X18,k1_tsep_1(sK1,X18,X19)) ) ),
    inference(resolution,[],[f63,f89])).

fof(f1245,plain,
    ( r1_tsep_1(sK3,k1_tsep_1(sK1,sK1,sK1))
    | ~ r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3))
    | ~ l1_pre_topc(k1_tsep_1(sK1,sK1,sK1)) ),
    inference(subsumption_resolution,[],[f1244,f51])).

fof(f1244,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK1,sK1,sK1))
    | ~ r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3))
    | r1_tsep_1(sK3,k1_tsep_1(sK1,sK1,sK1))
    | ~ l1_pre_topc(k1_tsep_1(sK1,sK1,sK1)) ),
    inference(resolution,[],[f883,f117])).

fof(f883,plain,
    ( r1_tsep_1(k1_tsep_1(sK1,sK1,sK1),sK3)
    | ~ l1_struct_0(k1_tsep_1(sK1,sK1,sK1))
    | ~ r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3)) ),
    inference(superposition,[],[f224,f866])).

fof(f224,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK3))
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f223,f88])).

fof(f223,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK3))
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X0,sK3)
      | ~ l1_pre_topc(sK3) ) ),
    inference(resolution,[],[f133,f51])).

fof(f133,plain,(
    ! [X3] :
      ( ~ l1_struct_0(sK3)
      | ~ r1_xboole_0(u1_struct_0(X3),k2_struct_0(sK3))
      | ~ l1_struct_0(X3)
      | r1_tsep_1(X3,sK3) ) ),
    inference(superposition,[],[f49,f98])).

fof(f191,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3))
    | ~ l1_struct_0(sK3)
    | r1_tsep_1(sK1,sK3) ),
    inference(superposition,[],[f187,f98])).

fof(f187,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k2_struct_0(sK1),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | r1_tsep_1(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f186,f89])).

fof(f186,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | ~ r1_xboole_0(k2_struct_0(sK1),u1_struct_0(X0))
      | r1_tsep_1(sK1,X0)
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f127,f51])).

fof(f127,plain,(
    ! [X1] :
      ( ~ l1_struct_0(sK1)
      | ~ l1_struct_0(X1)
      | ~ r1_xboole_0(k2_struct_0(sK1),u1_struct_0(X1))
      | r1_tsep_1(sK1,X1) ) ),
    inference(superposition,[],[f49,f96])).

fof(f1583,plain,
    ( r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3))
    | ~ l1_struct_0(sK3)
    | ~ r1_tsep_1(sK3,sK1) ),
    inference(resolution,[],[f1581,f297])).

fof(f297,plain,
    ( r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))
    | ~ l1_struct_0(sK3)
    | ~ r1_tsep_1(sK3,sK1) ),
    inference(superposition,[],[f292,f98])).

fof(f292,plain,(
    ! [X0] :
      ( r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK1))
      | ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f291,f89])).

fof(f291,plain,(
    ! [X0] :
      ( r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK1))
      | ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,sK1)
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f142,f51])).

fof(f142,plain,(
    ! [X1] :
      ( ~ l1_struct_0(sK1)
      | r1_xboole_0(u1_struct_0(X1),k2_struct_0(sK1))
      | ~ l1_struct_0(X1)
      | ~ r1_tsep_1(X1,sK1) ) ),
    inference(superposition,[],[f50,f96])).

fof(f1581,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))
    | r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f1580,f326])).

fof(f326,plain,(
    m1_pre_topc(sK3,sK3) ),
    inference(resolution,[],[f322,f39])).

fof(f1580,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))
    | r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3))
    | ~ m1_pre_topc(sK3,sK3) ),
    inference(subsumption_resolution,[],[f1579,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f1579,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))
    | r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK3) ),
    inference(duplicate_literal_removal,[],[f1578])).

fof(f1578,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))
    | r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK3) ),
    inference(resolution,[],[f1577,f683])).

fof(f683,plain,(
    ! [X4,X5] :
      ( l1_pre_topc(k1_tsep_1(sK3,X4,X5))
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,sK3)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,sK3) ) ),
    inference(resolution,[],[f641,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f88,f62])).

fof(f641,plain,(
    ! [X6,X7] :
      ( m1_pre_topc(k1_tsep_1(sK3,X6,X7),sK3)
      | ~ m1_pre_topc(X6,sK3)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X7,sK3)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f637,f38])).

fof(f637,plain,(
    ! [X6,X7] :
      ( v2_struct_0(sK3)
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X6,sK3)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X7,sK3)
      | m1_pre_topc(k1_tsep_1(sK3,X6,X7),sK3) ) ),
    inference(resolution,[],[f78,f88])).

fof(f1577,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK3,sK3,sK3))
    | ~ r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))
    | r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f1576,f51])).

fof(f1576,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))
    | ~ l1_pre_topc(k1_tsep_1(sK3,sK3,sK3))
    | ~ l1_struct_0(k1_tsep_1(sK3,sK3,sK3))
    | r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3)) ),
    inference(resolution,[],[f1371,f1198])).

fof(f1198,plain,
    ( ~ r1_tsep_1(sK1,k1_tsep_1(sK3,sK3,sK3))
    | ~ l1_struct_0(k1_tsep_1(sK3,sK3,sK3))
    | r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3)) ),
    inference(superposition,[],[f239,f1171])).

fof(f1171,plain,(
    k2_struct_0(sK3) = u1_struct_0(k1_tsep_1(sK3,sK3,sK3)) ),
    inference(subsumption_resolution,[],[f1170,f38])).

fof(f1170,plain,
    ( k2_struct_0(sK3) = u1_struct_0(k1_tsep_1(sK3,sK3,sK3))
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f1169,f326])).

fof(f1169,plain,
    ( k2_struct_0(sK3) = u1_struct_0(k1_tsep_1(sK3,sK3,sK3))
    | ~ m1_pre_topc(sK3,sK3)
    | v2_struct_0(sK3) ),
    inference(duplicate_literal_removal,[],[f1168])).

fof(f1168,plain,
    ( k2_struct_0(sK3) = u1_struct_0(k1_tsep_1(sK3,sK3,sK3))
    | ~ m1_pre_topc(sK3,sK3)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f1133,f641])).

fof(f1133,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK3,sK3,sK3),sK3)
    | k2_struct_0(sK3) = u1_struct_0(k1_tsep_1(sK3,sK3,sK3)) ),
    inference(resolution,[],[f1131,f605])).

fof(f605,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK3,X0)
      | ~ m1_pre_topc(X0,sK3)
      | u1_struct_0(X0) = k2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f599,f593])).

fof(f593,plain,(
    ! [X3] :
      ( r1_tarski(u1_struct_0(X3),k2_struct_0(sK3))
      | ~ m1_pre_topc(X3,sK3) ) ),
    inference(subsumption_resolution,[],[f591,f326])).

fof(f591,plain,(
    ! [X3] :
      ( r1_tarski(u1_struct_0(X3),k2_struct_0(sK3))
      | ~ m1_pre_topc(sK3,sK3)
      | ~ m1_pre_topc(X3,sK3) ) ),
    inference(duplicate_literal_removal,[],[f590])).

fof(f590,plain,(
    ! [X3] :
      ( r1_tarski(u1_struct_0(X3),k2_struct_0(sK3))
      | ~ m1_pre_topc(sK3,sK3)
      | ~ m1_pre_topc(X3,sK3)
      | ~ m1_pre_topc(X3,sK3) ) ),
    inference(superposition,[],[f236,f98])).

fof(f236,plain,(
    ! [X6,X7] :
      ( r1_tarski(u1_struct_0(X6),u1_struct_0(X7))
      | ~ m1_pre_topc(X7,sK3)
      | ~ m1_pre_topc(X6,X7)
      | ~ m1_pre_topc(X6,sK3) ) ),
    inference(subsumption_resolution,[],[f232,f104])).

fof(f104,plain,(
    v2_pre_topc(sK3) ),
    inference(resolution,[],[f103,f39])).

fof(f232,plain,(
    ! [X6,X7] :
      ( ~ v2_pre_topc(sK3)
      | ~ m1_pre_topc(X6,sK3)
      | ~ m1_pre_topc(X7,sK3)
      | ~ m1_pre_topc(X6,X7)
      | r1_tarski(u1_struct_0(X6),u1_struct_0(X7)) ) ),
    inference(resolution,[],[f67,f88])).

fof(f599,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | ~ m1_pre_topc(sK3,X0)
      | ~ r1_tarski(u1_struct_0(X0),k2_struct_0(sK3))
      | u1_struct_0(X0) = k2_struct_0(sK3) ) ),
    inference(resolution,[],[f592,f72])).

fof(f592,plain,(
    ! [X3] :
      ( r1_tarski(k2_struct_0(sK3),u1_struct_0(X3))
      | ~ m1_pre_topc(X3,sK3)
      | ~ m1_pre_topc(sK3,X3) ) ),
    inference(subsumption_resolution,[],[f586,f326])).

fof(f586,plain,(
    ! [X3] :
      ( r1_tarski(k2_struct_0(sK3),u1_struct_0(X3))
      | ~ m1_pre_topc(X3,sK3)
      | ~ m1_pre_topc(sK3,X3)
      | ~ m1_pre_topc(sK3,sK3) ) ),
    inference(superposition,[],[f236,f98])).

fof(f1131,plain,(
    m1_pre_topc(sK3,k1_tsep_1(sK3,sK3,sK3)) ),
    inference(subsumption_resolution,[],[f1130,f38])).

fof(f1130,plain,
    ( v2_struct_0(sK3)
    | m1_pre_topc(sK3,k1_tsep_1(sK3,sK3,sK3)) ),
    inference(resolution,[],[f1128,f326])).

fof(f1128,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK3)
      | v2_struct_0(X3)
      | m1_pre_topc(X3,k1_tsep_1(sK3,X3,sK3)) ) ),
    inference(subsumption_resolution,[],[f1127,f38])).

fof(f1127,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK3)
      | v2_struct_0(sK3)
      | v2_struct_0(X3)
      | m1_pre_topc(X3,k1_tsep_1(sK3,X3,sK3)) ) ),
    inference(resolution,[],[f794,f326])).

fof(f794,plain,(
    ! [X23,X22] :
      ( ~ m1_pre_topc(X23,sK3)
      | ~ m1_pre_topc(X22,sK3)
      | v2_struct_0(X23)
      | v2_struct_0(X22)
      | m1_pre_topc(X22,k1_tsep_1(sK3,X22,X23)) ) ),
    inference(subsumption_resolution,[],[f793,f38])).

fof(f793,plain,(
    ! [X23,X22] :
      ( v2_struct_0(sK3)
      | v2_struct_0(X22)
      | ~ m1_pre_topc(X22,sK3)
      | v2_struct_0(X23)
      | ~ m1_pre_topc(X23,sK3)
      | m1_pre_topc(X22,k1_tsep_1(sK3,X22,X23)) ) ),
    inference(subsumption_resolution,[],[f782,f104])).

fof(f782,plain,(
    ! [X23,X22] :
      ( ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | v2_struct_0(X22)
      | ~ m1_pre_topc(X22,sK3)
      | v2_struct_0(X23)
      | ~ m1_pre_topc(X23,sK3)
      | m1_pre_topc(X22,k1_tsep_1(sK3,X22,X23)) ) ),
    inference(resolution,[],[f63,f88])).

fof(f1371,plain,
    ( r1_tsep_1(sK1,k1_tsep_1(sK3,sK3,sK3))
    | ~ r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))
    | ~ l1_pre_topc(k1_tsep_1(sK3,sK3,sK3)) ),
    inference(subsumption_resolution,[],[f1370,f51])).

fof(f1370,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK3,sK3,sK3))
    | ~ r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))
    | r1_tsep_1(sK1,k1_tsep_1(sK3,sK3,sK3))
    | ~ l1_pre_topc(k1_tsep_1(sK3,sK3,sK3)) ),
    inference(resolution,[],[f1187,f115])).

fof(f115,plain,(
    ! [X1] :
      ( ~ r1_tsep_1(X1,sK1)
      | r1_tsep_1(sK1,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f113,f89])).

fof(f1187,plain,
    ( r1_tsep_1(k1_tsep_1(sK3,sK3,sK3),sK1)
    | ~ l1_struct_0(k1_tsep_1(sK3,sK3,sK3))
    | ~ r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) ),
    inference(superposition,[],[f210,f1171])).

fof(f210,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK1))
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f209,f89])).

fof(f209,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK1))
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X0,sK1)
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f131,f51])).

fof(f131,plain,(
    ! [X1] :
      ( ~ l1_struct_0(sK1)
      | ~ r1_xboole_0(u1_struct_0(X1),k2_struct_0(sK1))
      | ~ l1_struct_0(X1)
      | r1_tsep_1(X1,sK1) ) ),
    inference(superposition,[],[f49,f96])).

fof(f214,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))
    | ~ l1_struct_0(sK3)
    | r1_tsep_1(sK3,sK1) ),
    inference(superposition,[],[f210,f98])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:19:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (11101)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.47  % (11103)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.48  % (11121)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.49  % (11112)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.49  % (11100)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (11100)Refutation not found, incomplete strategy% (11100)------------------------------
% 0.21/0.50  % (11100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (11100)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (11100)Memory used [KB]: 10618
% 0.21/0.50  % (11100)Time elapsed: 0.082 s
% 0.21/0.50  % (11100)------------------------------
% 0.21/0.50  % (11100)------------------------------
% 0.21/0.50  % (11105)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (11113)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (11122)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (11113)Refutation not found, incomplete strategy% (11113)------------------------------
% 0.21/0.50  % (11113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (11113)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (11113)Memory used [KB]: 6140
% 0.21/0.50  % (11113)Time elapsed: 0.098 s
% 0.21/0.50  % (11113)------------------------------
% 0.21/0.50  % (11113)------------------------------
% 0.21/0.50  % (11102)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (11107)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (11110)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (11120)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (11123)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (11115)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (11104)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (11119)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (11108)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (11109)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (11117)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (11118)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (11111)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (11116)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (11106)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  % (11114)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.39/0.54  % (11125)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.39/0.54  % (11124)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 2.22/0.66  % (11109)Refutation not found, incomplete strategy% (11109)------------------------------
% 2.22/0.66  % (11109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.66  % (11109)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.66  
% 2.22/0.66  % (11109)Memory used [KB]: 6140
% 2.22/0.66  % (11109)Time elapsed: 0.241 s
% 2.22/0.66  % (11109)------------------------------
% 2.22/0.66  % (11109)------------------------------
% 3.73/0.84  % (11119)Refutation found. Thanks to Tanya!
% 3.73/0.84  % SZS status Theorem for theBenchmark
% 3.73/0.84  % SZS output start Proof for theBenchmark
% 3.73/0.84  fof(f4747,plain,(
% 3.73/0.84    $false),
% 3.73/0.84    inference(subsumption_resolution,[],[f4746,f88])).
% 3.73/0.84  fof(f88,plain,(
% 3.73/0.84    l1_pre_topc(sK3)),
% 3.73/0.84    inference(resolution,[],[f87,f39])).
% 3.73/0.84  fof(f39,plain,(
% 3.73/0.84    m1_pre_topc(sK3,sK0)),
% 3.73/0.84    inference(cnf_transformation,[],[f17])).
% 3.73/0.84  fof(f17,plain,(
% 3.73/0.84    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.73/0.84    inference(flattening,[],[f16])).
% 3.73/0.84  fof(f16,plain,(
% 3.73/0.84    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3))) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.73/0.84    inference(ennf_transformation,[],[f15])).
% 3.73/0.84  fof(f15,negated_conjecture,(
% 3.73/0.84    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 3.73/0.84    inference(negated_conjecture,[],[f14])).
% 3.73/0.84  fof(f14,conjecture,(
% 3.73/0.84    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 3.73/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).
% 3.73/0.84  fof(f87,plain,(
% 3.73/0.84    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 3.73/0.84    inference(resolution,[],[f62,f47])).
% 3.73/0.84  fof(f47,plain,(
% 3.73/0.84    l1_pre_topc(sK0)),
% 3.73/0.84    inference(cnf_transformation,[],[f17])).
% 3.73/0.84  fof(f62,plain,(
% 3.73/0.84    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 3.73/0.84    inference(cnf_transformation,[],[f22])).
% 3.73/0.84  fof(f22,plain,(
% 3.73/0.84    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.73/0.84    inference(ennf_transformation,[],[f7])).
% 3.73/0.84  fof(f7,axiom,(
% 3.73/0.84    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.73/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 3.73/0.84  fof(f4746,plain,(
% 3.73/0.84    ~l1_pre_topc(sK3)),
% 3.73/0.84    inference(resolution,[],[f4708,f51])).
% 3.73/0.84  fof(f51,plain,(
% 3.73/0.84    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.73/0.84    inference(cnf_transformation,[],[f20])).
% 3.73/0.84  fof(f20,plain,(
% 3.73/0.84    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.73/0.84    inference(ennf_transformation,[],[f6])).
% 3.73/0.84  fof(f6,axiom,(
% 3.73/0.84    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.73/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 3.73/0.84  fof(f4708,plain,(
% 3.73/0.84    ~l1_struct_0(sK3)),
% 3.73/0.84    inference(subsumption_resolution,[],[f1587,f4697])).
% 3.73/0.84  fof(f4697,plain,(
% 3.73/0.84    r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))),
% 3.73/0.84    inference(resolution,[],[f4586,f3136])).
% 3.73/0.84  fof(f3136,plain,(
% 3.73/0.84    r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2))),
% 3.73/0.84    inference(subsumption_resolution,[],[f3135,f2560])).
% 3.73/0.84  fof(f2560,plain,(
% 3.73/0.84    l1_pre_topc(k1_tsep_1(sK0,sK2,sK2))),
% 3.73/0.84    inference(subsumption_resolution,[],[f2559,f42])).
% 3.73/0.84  fof(f42,plain,(
% 3.73/0.84    m1_pre_topc(sK2,sK0)),
% 3.73/0.84    inference(cnf_transformation,[],[f17])).
% 3.73/0.84  fof(f2559,plain,(
% 3.73/0.84    ~m1_pre_topc(sK2,sK0) | l1_pre_topc(k1_tsep_1(sK0,sK2,sK2))),
% 3.73/0.84    inference(subsumption_resolution,[],[f2547,f41])).
% 3.73/0.84  fof(f41,plain,(
% 3.73/0.84    ~v2_struct_0(sK2)),
% 3.73/0.84    inference(cnf_transformation,[],[f17])).
% 3.73/0.84  fof(f2547,plain,(
% 3.73/0.84    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | l1_pre_topc(k1_tsep_1(sK0,sK2,sK2))),
% 3.73/0.84    inference(duplicate_literal_removal,[],[f2536])).
% 3.73/0.84  fof(f2536,plain,(
% 3.73/0.84    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | l1_pre_topc(k1_tsep_1(sK0,sK2,sK2))),
% 3.73/0.84    inference(resolution,[],[f642,f1711])).
% 3.73/0.84  fof(f1711,plain,(
% 3.73/0.84    ( ! [X4] : (~m1_pre_topc(X4,k1_tsep_1(sK0,sK2,sK2)) | l1_pre_topc(X4)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f1708,f41])).
% 3.73/0.84  fof(f1708,plain,(
% 3.73/0.84    ( ! [X4] : (v2_struct_0(sK2) | ~m1_pre_topc(X4,k1_tsep_1(sK0,sK2,sK2)) | l1_pre_topc(X4)) )),
% 3.73/0.84    inference(resolution,[],[f1658,f42])).
% 3.73/0.84  fof(f1658,plain,(
% 3.73/0.84    ( ! [X6,X7] : (~m1_pre_topc(X6,sK0) | v2_struct_0(X6) | ~m1_pre_topc(X7,k1_tsep_1(sK0,sK2,X6)) | l1_pre_topc(X7)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f1655,f41])).
% 3.73/0.84  fof(f1655,plain,(
% 3.73/0.84    ( ! [X6,X7] : (~m1_pre_topc(X6,sK0) | v2_struct_0(sK2) | v2_struct_0(X6) | ~m1_pre_topc(X7,k1_tsep_1(sK0,sK2,X6)) | l1_pre_topc(X7)) )),
% 3.73/0.84    inference(resolution,[],[f645,f42])).
% 3.73/0.84  fof(f645,plain,(
% 3.73/0.84    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_pre_topc(X2,k1_tsep_1(sK0,X1,X0)) | l1_pre_topc(X2)) )),
% 3.73/0.84    inference(resolution,[],[f644,f62])).
% 3.73/0.84  fof(f644,plain,(
% 3.73/0.84    ( ! [X4,X5] : (l1_pre_topc(k1_tsep_1(sK0,X4,X5)) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK0) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK0)) )),
% 3.73/0.84    inference(resolution,[],[f638,f87])).
% 3.73/0.84  fof(f638,plain,(
% 3.73/0.84    ( ! [X0,X1] : (m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X0)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f634,f45])).
% 3.73/0.84  fof(f45,plain,(
% 3.73/0.84    ~v2_struct_0(sK0)),
% 3.73/0.84    inference(cnf_transformation,[],[f17])).
% 3.73/0.84  fof(f634,plain,(
% 3.73/0.84    ( ! [X0,X1] : (v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)) )),
% 3.73/0.84    inference(resolution,[],[f78,f47])).
% 3.73/0.84  fof(f78,plain,(
% 3.73/0.84    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)) )),
% 3.73/0.84    inference(cnf_transformation,[],[f35])).
% 3.73/0.84  fof(f35,plain,(
% 3.73/0.84    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.73/0.84    inference(flattening,[],[f34])).
% 3.73/0.84  fof(f34,plain,(
% 3.73/0.84    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.73/0.84    inference(ennf_transformation,[],[f10])).
% 3.73/0.84  fof(f10,axiom,(
% 3.73/0.84    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 3.73/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 3.73/0.84  fof(f642,plain,(
% 3.73/0.84    ( ! [X0,X1] : (m1_pre_topc(k1_tsep_1(sK0,X0,X1),k1_tsep_1(sK0,X0,X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0)) )),
% 3.73/0.84    inference(resolution,[],[f638,f322])).
% 3.73/0.84  fof(f322,plain,(
% 3.73/0.84    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_pre_topc(X0,X0)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f318,f46])).
% 3.73/0.84  fof(f46,plain,(
% 3.73/0.84    v2_pre_topc(sK0)),
% 3.73/0.84    inference(cnf_transformation,[],[f17])).
% 3.73/0.84  fof(f318,plain,(
% 3.73/0.84    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_pre_topc(X0,X0) | ~v2_pre_topc(sK0)) )),
% 3.73/0.84    inference(resolution,[],[f314,f47])).
% 3.73/0.84  fof(f314,plain,(
% 3.73/0.84    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_pre_topc(X1,X1) | ~v2_pre_topc(X0)) )),
% 3.73/0.84    inference(duplicate_literal_removal,[],[f305])).
% 3.73/0.84  fof(f305,plain,(
% 3.73/0.84    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,X0) | m1_pre_topc(X1,X1) | ~v2_pre_topc(X0)) )),
% 3.73/0.84    inference(resolution,[],[f68,f81])).
% 3.73/0.84  fof(f81,plain,(
% 3.73/0.84    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.73/0.84    inference(equality_resolution,[],[f71])).
% 3.73/0.84  fof(f71,plain,(
% 3.73/0.84    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.73/0.84    inference(cnf_transformation,[],[f1])).
% 3.73/0.84  fof(f1,axiom,(
% 3.73/0.84    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.73/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.73/0.84  fof(f68,plain,(
% 3.73/0.84    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | m1_pre_topc(X1,X2) | ~v2_pre_topc(X0)) )),
% 3.73/0.84    inference(cnf_transformation,[],[f30])).
% 3.73/0.84  fof(f30,plain,(
% 3.73/0.84    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.73/0.84    inference(flattening,[],[f29])).
% 3.73/0.84  fof(f29,plain,(
% 3.73/0.84    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.73/0.84    inference(ennf_transformation,[],[f13])).
% 3.73/0.84  fof(f13,axiom,(
% 3.73/0.84    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 3.73/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 3.73/0.84  fof(f3135,plain,(
% 3.73/0.84    r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2)) | ~l1_pre_topc(k1_tsep_1(sK0,sK2,sK2))),
% 3.73/0.84    inference(resolution,[],[f3116,f51])).
% 3.73/0.84  fof(f3116,plain,(
% 3.73/0.84    ~l1_struct_0(k1_tsep_1(sK0,sK2,sK2)) | r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2))),
% 3.73/0.84    inference(subsumption_resolution,[],[f2070,f3114])).
% 3.73/0.84  fof(f3114,plain,(
% 3.73/0.84    r1_tsep_1(sK3,k1_tsep_1(sK0,sK2,sK2))),
% 3.73/0.84    inference(subsumption_resolution,[],[f3113,f2560])).
% 3.73/0.84  fof(f3113,plain,(
% 3.73/0.84    r1_tsep_1(sK3,k1_tsep_1(sK0,sK2,sK2)) | ~l1_pre_topc(k1_tsep_1(sK0,sK2,sK2))),
% 3.73/0.84    inference(subsumption_resolution,[],[f3112,f122])).
% 3.73/0.84  fof(f122,plain,(
% 3.73/0.84    r1_tsep_1(sK3,sK2)),
% 3.73/0.84    inference(subsumption_resolution,[],[f121,f90])).
% 3.73/0.84  fof(f90,plain,(
% 3.73/0.84    l1_pre_topc(sK2)),
% 3.73/0.84    inference(resolution,[],[f87,f42])).
% 3.73/0.84  fof(f121,plain,(
% 3.73/0.84    r1_tsep_1(sK3,sK2) | ~l1_pre_topc(sK2)),
% 3.73/0.84    inference(resolution,[],[f117,f120])).
% 3.73/0.84  fof(f120,plain,(
% 3.73/0.84    r1_tsep_1(sK2,sK3)),
% 3.73/0.84    inference(subsumption_resolution,[],[f119,f88])).
% 3.73/0.84  fof(f119,plain,(
% 3.73/0.84    r1_tsep_1(sK2,sK3) | ~l1_pre_topc(sK3)),
% 3.73/0.84    inference(duplicate_literal_removal,[],[f118])).
% 3.73/0.84  fof(f118,plain,(
% 3.73/0.84    r1_tsep_1(sK2,sK3) | ~l1_pre_topc(sK3) | r1_tsep_1(sK2,sK3)),
% 3.73/0.84    inference(resolution,[],[f116,f36])).
% 3.73/0.84  fof(f36,plain,(
% 3.73/0.84    r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)),
% 3.73/0.84    inference(cnf_transformation,[],[f17])).
% 3.73/0.84  fof(f116,plain,(
% 3.73/0.84    ( ! [X2] : (~r1_tsep_1(X2,sK2) | r1_tsep_1(sK2,X2) | ~l1_pre_topc(X2)) )),
% 3.73/0.84    inference(resolution,[],[f113,f90])).
% 3.73/0.84  fof(f113,plain,(
% 3.73/0.84    ( ! [X0,X1] : (~l1_pre_topc(X1) | r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_pre_topc(X0)) )),
% 3.73/0.84    inference(resolution,[],[f112,f51])).
% 3.73/0.84  fof(f112,plain,(
% 3.73/0.84    ( ! [X0,X1] : (~l1_struct_0(X0) | ~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_pre_topc(X1)) )),
% 3.73/0.84    inference(resolution,[],[f69,f51])).
% 3.73/0.84  fof(f69,plain,(
% 3.73/0.84    ( ! [X0,X1] : (~l1_struct_0(X1) | ~l1_struct_0(X0) | ~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0)) )),
% 3.73/0.84    inference(cnf_transformation,[],[f32])).
% 3.73/0.84  fof(f32,plain,(
% 3.73/0.84    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 3.73/0.84    inference(flattening,[],[f31])).
% 3.73/0.84  fof(f31,plain,(
% 3.73/0.84    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 3.73/0.84    inference(ennf_transformation,[],[f11])).
% 3.73/0.84  fof(f11,axiom,(
% 3.73/0.84    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 3.73/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 3.73/0.84  fof(f117,plain,(
% 3.73/0.84    ( ! [X3] : (~r1_tsep_1(X3,sK3) | r1_tsep_1(sK3,X3) | ~l1_pre_topc(X3)) )),
% 3.73/0.84    inference(resolution,[],[f113,f88])).
% 3.73/0.84  fof(f3112,plain,(
% 3.73/0.84    ~r1_tsep_1(sK3,sK2) | r1_tsep_1(sK3,k1_tsep_1(sK0,sK2,sK2)) | ~l1_pre_topc(k1_tsep_1(sK0,sK2,sK2))),
% 3.73/0.84    inference(subsumption_resolution,[],[f3086,f88])).
% 3.73/0.84  fof(f3086,plain,(
% 3.73/0.84    ~l1_pre_topc(sK3) | ~r1_tsep_1(sK3,sK2) | r1_tsep_1(sK3,k1_tsep_1(sK0,sK2,sK2)) | ~l1_pre_topc(k1_tsep_1(sK0,sK2,sK2))),
% 3.73/0.84    inference(resolution,[],[f3054,f117])).
% 3.73/0.84  fof(f3054,plain,(
% 3.73/0.84    ( ! [X0] : (r1_tsep_1(k1_tsep_1(sK0,sK2,sK2),X0) | ~l1_pre_topc(X0) | ~r1_tsep_1(X0,sK2)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f3044,f51])).
% 3.73/0.84  fof(f3044,plain,(
% 3.73/0.84    ( ! [X0] : (r1_tsep_1(k1_tsep_1(sK0,sK2,sK2),X0) | ~l1_pre_topc(X0) | ~l1_struct_0(X0) | ~r1_tsep_1(X0,sK2)) )),
% 3.73/0.84    inference(resolution,[],[f2597,f2357])).
% 3.73/0.84  fof(f2357,plain,(
% 3.73/0.84    ( ! [X0] : (r1_tsep_1(X0,k1_tsep_1(sK0,sK2,sK2)) | ~l1_struct_0(X0) | ~r1_tsep_1(X0,sK2)) )),
% 3.73/0.84    inference(duplicate_literal_removal,[],[f2348])).
% 3.73/0.84  fof(f2348,plain,(
% 3.73/0.84    ( ! [X0] : (r1_tsep_1(X0,k1_tsep_1(sK0,sK2,sK2)) | ~l1_struct_0(X0) | ~l1_struct_0(X0) | ~r1_tsep_1(X0,sK2)) )),
% 3.73/0.84    inference(resolution,[],[f2347,f340])).
% 3.73/0.84  fof(f340,plain,(
% 3.73/0.84    ( ! [X0] : (r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK2)) | ~l1_struct_0(X0) | ~r1_tsep_1(X0,sK2)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f339,f90])).
% 3.73/0.84  fof(f339,plain,(
% 3.73/0.84    ( ! [X0] : (r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK2)) | ~l1_struct_0(X0) | ~r1_tsep_1(X0,sK2) | ~l1_pre_topc(sK2)) )),
% 3.73/0.84    inference(resolution,[],[f143,f51])).
% 3.73/0.84  fof(f143,plain,(
% 3.73/0.84    ( ! [X2] : (~l1_struct_0(sK2) | r1_xboole_0(u1_struct_0(X2),k2_struct_0(sK2)) | ~l1_struct_0(X2) | ~r1_tsep_1(X2,sK2)) )),
% 3.73/0.84    inference(superposition,[],[f50,f97])).
% 3.73/0.84  fof(f97,plain,(
% 3.73/0.84    k2_struct_0(sK2) = u1_struct_0(sK2)),
% 3.73/0.84    inference(resolution,[],[f86,f90])).
% 3.73/0.84  fof(f86,plain,(
% 3.73/0.84    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 3.73/0.84    inference(resolution,[],[f48,f51])).
% 3.73/0.84  fof(f48,plain,(
% 3.73/0.84    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 3.73/0.84    inference(cnf_transformation,[],[f18])).
% 3.73/0.84  fof(f18,plain,(
% 3.73/0.84    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.73/0.84    inference(ennf_transformation,[],[f4])).
% 3.73/0.84  fof(f4,axiom,(
% 3.73/0.84    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.73/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 3.73/0.84  fof(f50,plain,(
% 3.73/0.84    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | ~r1_tsep_1(X0,X1)) )),
% 3.73/0.84    inference(cnf_transformation,[],[f19])).
% 3.73/0.84  fof(f19,plain,(
% 3.73/0.84    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.73/0.84    inference(ennf_transformation,[],[f9])).
% 3.73/0.84  fof(f9,axiom,(
% 3.73/0.84    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 3.73/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).
% 3.73/0.84  fof(f2347,plain,(
% 3.73/0.84    ( ! [X0] : (~r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK2)) | r1_tsep_1(X0,k1_tsep_1(sK0,sK2,sK2)) | ~l1_struct_0(X0)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f2346,f42])).
% 3.73/0.84  fof(f2346,plain,(
% 3.73/0.84    ( ! [X0] : (~l1_struct_0(X0) | r1_tsep_1(X0,k1_tsep_1(sK0,sK2,sK2)) | ~r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK2)) | ~m1_pre_topc(sK2,sK0)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f2345,f41])).
% 3.73/0.84  fof(f2345,plain,(
% 3.73/0.84    ( ! [X0] : (~l1_struct_0(X0) | r1_tsep_1(X0,k1_tsep_1(sK0,sK2,sK2)) | ~r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK2)) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0)) )),
% 3.73/0.84    inference(duplicate_literal_removal,[],[f2344])).
% 3.73/0.84  fof(f2344,plain,(
% 3.73/0.84    ( ! [X0] : (~l1_struct_0(X0) | r1_tsep_1(X0,k1_tsep_1(sK0,sK2,sK2)) | ~r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK2)) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0)) )),
% 3.73/0.84    inference(resolution,[],[f2242,f644])).
% 3.73/0.84  fof(f2242,plain,(
% 3.73/0.84    ( ! [X0] : (~l1_pre_topc(k1_tsep_1(sK0,sK2,sK2)) | ~l1_struct_0(X0) | r1_tsep_1(X0,k1_tsep_1(sK0,sK2,sK2)) | ~r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK2))) )),
% 3.73/0.84    inference(resolution,[],[f2072,f51])).
% 3.73/0.84  fof(f2072,plain,(
% 3.73/0.84    ( ! [X1] : (~l1_struct_0(k1_tsep_1(sK0,sK2,sK2)) | ~r1_xboole_0(u1_struct_0(X1),k2_struct_0(sK2)) | ~l1_struct_0(X1) | r1_tsep_1(X1,k1_tsep_1(sK0,sK2,sK2))) )),
% 3.73/0.84    inference(resolution,[],[f2052,f49])).
% 3.73/0.84  fof(f49,plain,(
% 3.73/0.84    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | r1_tsep_1(X0,X1)) )),
% 3.73/0.84    inference(cnf_transformation,[],[f19])).
% 3.73/0.84  fof(f2052,plain,(
% 3.73/0.84    ( ! [X0] : (r1_xboole_0(X0,u1_struct_0(k1_tsep_1(sK0,sK2,sK2))) | ~r1_xboole_0(X0,k2_struct_0(sK2))) )),
% 3.73/0.84    inference(duplicate_literal_removal,[],[f2049])).
% 3.73/0.84  fof(f2049,plain,(
% 3.73/0.84    ( ! [X0] : (r1_xboole_0(X0,u1_struct_0(k1_tsep_1(sK0,sK2,sK2))) | ~r1_xboole_0(X0,k2_struct_0(sK2)) | ~r1_xboole_0(X0,k2_struct_0(sK2))) )),
% 3.73/0.84    inference(superposition,[],[f75,f2043])).
% 3.73/0.84  fof(f2043,plain,(
% 3.73/0.84    u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) = k2_xboole_0(k2_struct_0(sK2),k2_struct_0(sK2))),
% 3.73/0.84    inference(forward_demodulation,[],[f2042,f97])).
% 3.73/0.84  fof(f2042,plain,(
% 3.73/0.84    u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) = k2_xboole_0(u1_struct_0(sK2),k2_struct_0(sK2))),
% 3.73/0.84    inference(subsumption_resolution,[],[f2038,f41])).
% 3.73/0.84  fof(f2038,plain,(
% 3.73/0.84    u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) = k2_xboole_0(u1_struct_0(sK2),k2_struct_0(sK2)) | v2_struct_0(sK2)),
% 3.73/0.84    inference(resolution,[],[f1966,f42])).
% 3.73/0.84  fof(f1966,plain,(
% 3.73/0.84    ( ! [X4] : (~m1_pre_topc(X4,sK0) | k2_xboole_0(u1_struct_0(X4),k2_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,X4,sK2)) | v2_struct_0(X4)) )),
% 3.73/0.84    inference(forward_demodulation,[],[f1965,f97])).
% 3.73/0.84  fof(f1965,plain,(
% 3.73/0.84    ( ! [X4] : (~m1_pre_topc(X4,sK0) | v2_struct_0(X4) | k2_xboole_0(u1_struct_0(X4),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,X4,sK2))) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f1961,f41])).
% 3.73/0.84  fof(f1961,plain,(
% 3.73/0.84    ( ! [X4] : (~m1_pre_topc(X4,sK0) | v2_struct_0(sK2) | v2_struct_0(X4) | k2_xboole_0(u1_struct_0(X4),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,X4,sK2))) )),
% 3.73/0.84    inference(resolution,[],[f1336,f42])).
% 3.73/0.84  fof(f1336,plain,(
% 3.73/0.84    ( ! [X17,X16] : (~m1_pre_topc(X17,sK0) | ~m1_pre_topc(X16,sK0) | v2_struct_0(X17) | v2_struct_0(X16) | k2_xboole_0(u1_struct_0(X16),u1_struct_0(X17)) = u1_struct_0(k1_tsep_1(sK0,X16,X17))) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f1332,f45])).
% 3.73/0.84  fof(f1332,plain,(
% 3.73/0.84    ( ! [X17,X16] : (v2_struct_0(sK0) | v2_struct_0(X16) | ~m1_pre_topc(X16,sK0) | v2_struct_0(X17) | ~m1_pre_topc(X17,sK0) | k2_xboole_0(u1_struct_0(X16),u1_struct_0(X17)) = u1_struct_0(k1_tsep_1(sK0,X16,X17))) )),
% 3.73/0.84    inference(resolution,[],[f85,f47])).
% 3.73/0.84  fof(f85,plain,(
% 3.73/0.84    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f84,f76])).
% 3.73/0.84  fof(f76,plain,(
% 3.73/0.84    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 3.73/0.84    inference(cnf_transformation,[],[f35])).
% 3.73/0.84  fof(f84,plain,(
% 3.73/0.84    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f83,f77])).
% 3.73/0.84  fof(f77,plain,(
% 3.73/0.84    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 3.73/0.84    inference(cnf_transformation,[],[f35])).
% 3.73/0.84  fof(f83,plain,(
% 3.73/0.84    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f80,f78])).
% 3.73/0.84  fof(f80,plain,(
% 3.73/0.84    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))) )),
% 3.73/0.84    inference(equality_resolution,[],[f65])).
% 3.73/0.84  fof(f65,plain,(
% 3.73/0.84    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~v1_pre_topc(X3) | ~m1_pre_topc(X3,X0) | u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3) )),
% 3.73/0.84    inference(cnf_transformation,[],[f26])).
% 3.73/0.84  fof(f26,plain,(
% 3.73/0.84    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.73/0.84    inference(flattening,[],[f25])).
% 3.73/0.84  fof(f25,plain,(
% 3.73/0.84    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.73/0.84    inference(ennf_transformation,[],[f8])).
% 3.73/0.84  fof(f8,axiom,(
% 3.73/0.84    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 3.73/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).
% 3.73/0.84  fof(f75,plain,(
% 3.73/0.84    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 3.73/0.84    inference(cnf_transformation,[],[f33])).
% 3.73/0.84  fof(f33,plain,(
% 3.73/0.84    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.73/0.84    inference(ennf_transformation,[],[f2])).
% 3.73/0.84  fof(f2,axiom,(
% 3.73/0.84    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.73/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 3.73/0.84  fof(f2597,plain,(
% 3.73/0.84    ( ! [X12] : (~r1_tsep_1(X12,k1_tsep_1(sK0,sK2,sK2)) | r1_tsep_1(k1_tsep_1(sK0,sK2,sK2),X12) | ~l1_pre_topc(X12)) )),
% 3.73/0.84    inference(resolution,[],[f2560,f113])).
% 3.73/0.84  fof(f2070,plain,(
% 3.73/0.84    ~r1_tsep_1(sK3,k1_tsep_1(sK0,sK2,sK2)) | ~l1_struct_0(k1_tsep_1(sK0,sK2,sK2)) | r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK2))),
% 3.73/0.84    inference(resolution,[],[f2050,f275])).
% 3.73/0.84  fof(f275,plain,(
% 3.73/0.84    ( ! [X0] : (r1_xboole_0(k2_struct_0(sK3),u1_struct_0(X0)) | ~l1_struct_0(X0) | ~r1_tsep_1(sK3,X0)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f274,f88])).
% 3.73/0.84  fof(f274,plain,(
% 3.73/0.84    ( ! [X0] : (~l1_struct_0(X0) | r1_xboole_0(k2_struct_0(sK3),u1_struct_0(X0)) | ~r1_tsep_1(sK3,X0) | ~l1_pre_topc(sK3)) )),
% 3.73/0.84    inference(resolution,[],[f140,f51])).
% 3.73/0.84  fof(f140,plain,(
% 3.73/0.84    ( ! [X3] : (~l1_struct_0(sK3) | ~l1_struct_0(X3) | r1_xboole_0(k2_struct_0(sK3),u1_struct_0(X3)) | ~r1_tsep_1(sK3,X3)) )),
% 3.73/0.84    inference(superposition,[],[f50,f98])).
% 3.73/0.84  fof(f98,plain,(
% 3.73/0.84    k2_struct_0(sK3) = u1_struct_0(sK3)),
% 3.73/0.84    inference(resolution,[],[f86,f88])).
% 3.73/0.84  fof(f2050,plain,(
% 3.73/0.84    ( ! [X1] : (~r1_xboole_0(X1,u1_struct_0(k1_tsep_1(sK0,sK2,sK2))) | r1_xboole_0(X1,k2_struct_0(sK2))) )),
% 3.73/0.84    inference(superposition,[],[f74,f2043])).
% 3.73/0.84  fof(f74,plain,(
% 3.73/0.84    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 3.73/0.84    inference(cnf_transformation,[],[f33])).
% 3.73/0.84  fof(f4586,plain,(
% 3.73/0.84    ( ! [X1] : (~r1_xboole_0(X1,k2_struct_0(sK2)) | r1_xboole_0(X1,k2_struct_0(sK1))) )),
% 3.73/0.84    inference(backward_demodulation,[],[f3778,f4583])).
% 3.73/0.84  fof(f4583,plain,(
% 3.73/0.84    k2_struct_0(sK2) = k2_struct_0(k1_tsep_1(sK0,sK2,sK1))),
% 3.73/0.84    inference(forward_demodulation,[],[f4582,f989])).
% 3.73/0.84  fof(f989,plain,(
% 3.73/0.84    k2_struct_0(sK2) = u1_struct_0(k1_tsep_1(sK2,sK2,sK1))),
% 3.73/0.84    inference(subsumption_resolution,[],[f988,f41])).
% 3.73/0.84  fof(f988,plain,(
% 3.73/0.84    k2_struct_0(sK2) = u1_struct_0(k1_tsep_1(sK2,sK2,sK1)) | v2_struct_0(sK2)),
% 3.73/0.84    inference(subsumption_resolution,[],[f987,f40])).
% 3.73/0.84  fof(f40,plain,(
% 3.73/0.84    m1_pre_topc(sK1,sK2)),
% 3.73/0.84    inference(cnf_transformation,[],[f17])).
% 3.73/0.84  fof(f987,plain,(
% 3.73/0.84    k2_struct_0(sK2) = u1_struct_0(k1_tsep_1(sK2,sK2,sK1)) | ~m1_pre_topc(sK1,sK2) | v2_struct_0(sK2)),
% 3.73/0.84    inference(subsumption_resolution,[],[f986,f43])).
% 3.73/0.84  fof(f43,plain,(
% 3.73/0.84    ~v2_struct_0(sK1)),
% 3.73/0.84    inference(cnf_transformation,[],[f17])).
% 3.73/0.84  fof(f986,plain,(
% 3.73/0.84    k2_struct_0(sK2) = u1_struct_0(k1_tsep_1(sK2,sK2,sK1)) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK2) | v2_struct_0(sK2)),
% 3.73/0.84    inference(subsumption_resolution,[],[f985,f328])).
% 3.73/0.84  fof(f328,plain,(
% 3.73/0.84    m1_pre_topc(sK2,sK2)),
% 3.73/0.84    inference(resolution,[],[f322,f42])).
% 3.73/0.84  fof(f985,plain,(
% 3.73/0.84    k2_struct_0(sK2) = u1_struct_0(k1_tsep_1(sK2,sK2,sK1)) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK2) | v2_struct_0(sK2)),
% 3.73/0.84    inference(resolution,[],[f937,f640])).
% 3.73/0.84  fof(f640,plain,(
% 3.73/0.84    ( ! [X4,X5] : (m1_pre_topc(k1_tsep_1(sK2,X4,X5),sK2) | ~m1_pre_topc(X4,sK2) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK2) | v2_struct_0(X4)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f636,f41])).
% 3.73/0.84  fof(f636,plain,(
% 3.73/0.84    ( ! [X4,X5] : (v2_struct_0(sK2) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK2) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK2) | m1_pre_topc(k1_tsep_1(sK2,X4,X5),sK2)) )),
% 3.73/0.84    inference(resolution,[],[f78,f90])).
% 3.73/0.84  fof(f937,plain,(
% 3.73/0.84    ~m1_pre_topc(k1_tsep_1(sK2,sK2,sK1),sK2) | k2_struct_0(sK2) = u1_struct_0(k1_tsep_1(sK2,sK2,sK1))),
% 3.73/0.84    inference(resolution,[],[f933,f564])).
% 3.73/0.84  fof(f564,plain,(
% 3.73/0.84    ( ! [X0] : (~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X0,sK2) | u1_struct_0(X0) = k2_struct_0(sK2)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f558,f543])).
% 3.73/0.84  fof(f543,plain,(
% 3.73/0.84    ( ! [X2] : (r1_tarski(u1_struct_0(X2),k2_struct_0(sK2)) | ~m1_pre_topc(X2,sK2)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f540,f328])).
% 3.73/0.84  fof(f540,plain,(
% 3.73/0.84    ( ! [X2] : (r1_tarski(u1_struct_0(X2),k2_struct_0(sK2)) | ~m1_pre_topc(sK2,sK2) | ~m1_pre_topc(X2,sK2)) )),
% 3.73/0.84    inference(duplicate_literal_removal,[],[f538])).
% 3.73/0.84  fof(f538,plain,(
% 3.73/0.84    ( ! [X2] : (r1_tarski(u1_struct_0(X2),k2_struct_0(sK2)) | ~m1_pre_topc(sK2,sK2) | ~m1_pre_topc(X2,sK2) | ~m1_pre_topc(X2,sK2)) )),
% 3.73/0.84    inference(superposition,[],[f235,f97])).
% 3.73/0.84  fof(f235,plain,(
% 3.73/0.84    ( ! [X4,X5] : (r1_tarski(u1_struct_0(X4),u1_struct_0(X5)) | ~m1_pre_topc(X5,sK2) | ~m1_pre_topc(X4,X5) | ~m1_pre_topc(X4,sK2)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f231,f106])).
% 3.73/0.84  fof(f106,plain,(
% 3.73/0.84    v2_pre_topc(sK2)),
% 3.73/0.84    inference(resolution,[],[f103,f42])).
% 3.73/0.84  fof(f103,plain,(
% 3.73/0.84    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_pre_topc(X0)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f99,f46])).
% 3.73/0.84  fof(f99,plain,(
% 3.73/0.84    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_pre_topc(X0)) )),
% 3.73/0.84    inference(resolution,[],[f66,f47])).
% 3.73/0.84  fof(f66,plain,(
% 3.73/0.84    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1)) )),
% 3.73/0.84    inference(cnf_transformation,[],[f28])).
% 3.73/0.84  fof(f28,plain,(
% 3.73/0.84    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.73/0.84    inference(flattening,[],[f27])).
% 3.73/0.84  fof(f27,plain,(
% 3.73/0.84    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.73/0.84    inference(ennf_transformation,[],[f3])).
% 3.73/0.84  fof(f3,axiom,(
% 3.73/0.84    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.73/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 3.73/0.84  fof(f231,plain,(
% 3.73/0.84    ( ! [X4,X5] : (~v2_pre_topc(sK2) | ~m1_pre_topc(X4,sK2) | ~m1_pre_topc(X5,sK2) | ~m1_pre_topc(X4,X5) | r1_tarski(u1_struct_0(X4),u1_struct_0(X5))) )),
% 3.73/0.84    inference(resolution,[],[f67,f90])).
% 3.73/0.84  fof(f67,plain,(
% 3.73/0.84    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 3.73/0.84    inference(cnf_transformation,[],[f30])).
% 3.73/0.84  fof(f558,plain,(
% 3.73/0.84    ( ! [X0] : (~m1_pre_topc(X0,sK2) | ~m1_pre_topc(sK2,X0) | ~r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) | u1_struct_0(X0) = k2_struct_0(sK2)) )),
% 3.73/0.84    inference(resolution,[],[f542,f72])).
% 3.73/0.84  fof(f72,plain,(
% 3.73/0.84    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 3.73/0.84    inference(cnf_transformation,[],[f1])).
% 3.73/0.84  fof(f542,plain,(
% 3.73/0.84    ( ! [X2] : (r1_tarski(k2_struct_0(sK2),u1_struct_0(X2)) | ~m1_pre_topc(X2,sK2) | ~m1_pre_topc(sK2,X2)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f534,f328])).
% 3.73/0.84  fof(f534,plain,(
% 3.73/0.84    ( ! [X2] : (r1_tarski(k2_struct_0(sK2),u1_struct_0(X2)) | ~m1_pre_topc(X2,sK2) | ~m1_pre_topc(sK2,X2) | ~m1_pre_topc(sK2,sK2)) )),
% 3.73/0.84    inference(superposition,[],[f235,f97])).
% 3.73/0.84  fof(f933,plain,(
% 3.73/0.84    m1_pre_topc(sK2,k1_tsep_1(sK2,sK2,sK1))),
% 3.73/0.84    inference(subsumption_resolution,[],[f931,f41])).
% 3.73/0.84  fof(f931,plain,(
% 3.73/0.84    v2_struct_0(sK2) | m1_pre_topc(sK2,k1_tsep_1(sK2,sK2,sK1))),
% 3.73/0.84    inference(resolution,[],[f927,f328])).
% 3.73/0.84  fof(f927,plain,(
% 3.73/0.84    ( ! [X3] : (~m1_pre_topc(X3,sK2) | v2_struct_0(X3) | m1_pre_topc(X3,k1_tsep_1(sK2,X3,sK1))) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f925,f43])).
% 3.73/0.84  fof(f925,plain,(
% 3.73/0.84    ( ! [X3] : (~m1_pre_topc(X3,sK2) | v2_struct_0(sK1) | v2_struct_0(X3) | m1_pre_topc(X3,k1_tsep_1(sK2,X3,sK1))) )),
% 3.73/0.84    inference(resolution,[],[f792,f40])).
% 3.73/0.84  fof(f792,plain,(
% 3.73/0.84    ( ! [X21,X20] : (~m1_pre_topc(X21,sK2) | ~m1_pre_topc(X20,sK2) | v2_struct_0(X21) | v2_struct_0(X20) | m1_pre_topc(X20,k1_tsep_1(sK2,X20,X21))) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f791,f41])).
% 3.73/0.84  fof(f791,plain,(
% 3.73/0.84    ( ! [X21,X20] : (v2_struct_0(sK2) | v2_struct_0(X20) | ~m1_pre_topc(X20,sK2) | v2_struct_0(X21) | ~m1_pre_topc(X21,sK2) | m1_pre_topc(X20,k1_tsep_1(sK2,X20,X21))) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f781,f106])).
% 3.73/0.84  fof(f781,plain,(
% 3.73/0.84    ( ! [X21,X20] : (~v2_pre_topc(sK2) | v2_struct_0(sK2) | v2_struct_0(X20) | ~m1_pre_topc(X20,sK2) | v2_struct_0(X21) | ~m1_pre_topc(X21,sK2) | m1_pre_topc(X20,k1_tsep_1(sK2,X20,X21))) )),
% 3.73/0.84    inference(resolution,[],[f63,f90])).
% 3.73/0.84  fof(f63,plain,(
% 3.73/0.84    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))) )),
% 3.73/0.84    inference(cnf_transformation,[],[f24])).
% 3.73/0.84  fof(f24,plain,(
% 3.73/0.84    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.73/0.84    inference(flattening,[],[f23])).
% 3.73/0.84  fof(f23,plain,(
% 3.73/0.84    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.73/0.84    inference(ennf_transformation,[],[f12])).
% 3.73/0.84  fof(f12,axiom,(
% 3.73/0.84    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)))))),
% 3.73/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tsep_1)).
% 3.73/0.84  fof(f4582,plain,(
% 3.73/0.84    k2_struct_0(k1_tsep_1(sK0,sK2,sK1)) = u1_struct_0(k1_tsep_1(sK2,sK2,sK1))),
% 3.73/0.84    inference(forward_demodulation,[],[f4581,f3780])).
% 3.73/0.84  fof(f3780,plain,(
% 3.73/0.84    k2_struct_0(k1_tsep_1(sK0,sK2,sK1)) = k2_xboole_0(k2_struct_0(sK2),k2_struct_0(sK1))),
% 3.73/0.84    inference(backward_demodulation,[],[f1978,f3776])).
% 3.73/0.84  fof(f3776,plain,(
% 3.73/0.84    k2_struct_0(k1_tsep_1(sK0,sK2,sK1)) = u1_struct_0(k1_tsep_1(sK0,sK2,sK1))),
% 3.73/0.84    inference(subsumption_resolution,[],[f3773,f43])).
% 3.73/0.84  fof(f3773,plain,(
% 3.73/0.84    v2_struct_0(sK1) | k2_struct_0(k1_tsep_1(sK0,sK2,sK1)) = u1_struct_0(k1_tsep_1(sK0,sK2,sK1))),
% 3.73/0.84    inference(resolution,[],[f3183,f44])).
% 3.73/0.84  fof(f44,plain,(
% 3.73/0.84    m1_pre_topc(sK1,sK0)),
% 3.73/0.84    inference(cnf_transformation,[],[f17])).
% 3.73/0.84  fof(f3183,plain,(
% 3.73/0.84    ( ! [X4] : (~m1_pre_topc(X4,sK0) | v2_struct_0(X4) | k2_struct_0(k1_tsep_1(sK0,sK2,X4)) = u1_struct_0(k1_tsep_1(sK0,sK2,X4))) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f3180,f41])).
% 3.73/0.84  fof(f3180,plain,(
% 3.73/0.84    ( ! [X4] : (~m1_pre_topc(X4,sK0) | v2_struct_0(sK2) | v2_struct_0(X4) | k2_struct_0(k1_tsep_1(sK0,sK2,X4)) = u1_struct_0(k1_tsep_1(sK0,sK2,X4))) )),
% 3.73/0.84    inference(resolution,[],[f649,f42])).
% 3.73/0.84  fof(f649,plain,(
% 3.73/0.84    ( ! [X14,X15] : (~m1_pre_topc(X15,sK0) | ~m1_pre_topc(X14,sK0) | v2_struct_0(X15) | v2_struct_0(X14) | k2_struct_0(k1_tsep_1(sK0,X15,X14)) = u1_struct_0(k1_tsep_1(sK0,X15,X14))) )),
% 3.73/0.84    inference(resolution,[],[f644,f86])).
% 3.73/0.84  fof(f1978,plain,(
% 3.73/0.84    u1_struct_0(k1_tsep_1(sK0,sK2,sK1)) = k2_xboole_0(k2_struct_0(sK2),k2_struct_0(sK1))),
% 3.73/0.84    inference(forward_demodulation,[],[f1977,f97])).
% 3.73/0.84  fof(f1977,plain,(
% 3.73/0.84    u1_struct_0(k1_tsep_1(sK0,sK2,sK1)) = k2_xboole_0(u1_struct_0(sK2),k2_struct_0(sK1))),
% 3.73/0.84    inference(subsumption_resolution,[],[f1973,f41])).
% 3.73/0.84  fof(f1973,plain,(
% 3.73/0.84    u1_struct_0(k1_tsep_1(sK0,sK2,sK1)) = k2_xboole_0(u1_struct_0(sK2),k2_struct_0(sK1)) | v2_struct_0(sK2)),
% 3.73/0.84    inference(resolution,[],[f1964,f42])).
% 3.73/0.84  fof(f1964,plain,(
% 3.73/0.84    ( ! [X3] : (~m1_pre_topc(X3,sK0) | u1_struct_0(k1_tsep_1(sK0,X3,sK1)) = k2_xboole_0(u1_struct_0(X3),k2_struct_0(sK1)) | v2_struct_0(X3)) )),
% 3.73/0.84    inference(forward_demodulation,[],[f1963,f96])).
% 3.73/0.84  fof(f96,plain,(
% 3.73/0.84    k2_struct_0(sK1) = u1_struct_0(sK1)),
% 3.73/0.84    inference(resolution,[],[f86,f89])).
% 3.73/0.84  fof(f89,plain,(
% 3.73/0.84    l1_pre_topc(sK1)),
% 3.73/0.84    inference(resolution,[],[f87,f44])).
% 3.73/0.84  fof(f1963,plain,(
% 3.73/0.84    ( ! [X3] : (~m1_pre_topc(X3,sK0) | v2_struct_0(X3) | k2_xboole_0(u1_struct_0(X3),u1_struct_0(sK1)) = u1_struct_0(k1_tsep_1(sK0,X3,sK1))) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f1960,f43])).
% 3.73/0.84  fof(f1960,plain,(
% 3.73/0.84    ( ! [X3] : (~m1_pre_topc(X3,sK0) | v2_struct_0(sK1) | v2_struct_0(X3) | k2_xboole_0(u1_struct_0(X3),u1_struct_0(sK1)) = u1_struct_0(k1_tsep_1(sK0,X3,sK1))) )),
% 3.73/0.84    inference(resolution,[],[f1336,f44])).
% 3.73/0.84  fof(f4581,plain,(
% 3.73/0.84    u1_struct_0(k1_tsep_1(sK2,sK2,sK1)) = k2_xboole_0(k2_struct_0(sK2),k2_struct_0(sK1))),
% 3.73/0.84    inference(forward_demodulation,[],[f4580,f97])).
% 3.73/0.84  fof(f4580,plain,(
% 3.73/0.84    u1_struct_0(k1_tsep_1(sK2,sK2,sK1)) = k2_xboole_0(u1_struct_0(sK2),k2_struct_0(sK1))),
% 3.73/0.84    inference(subsumption_resolution,[],[f4576,f41])).
% 3.73/0.84  fof(f4576,plain,(
% 3.73/0.84    u1_struct_0(k1_tsep_1(sK2,sK2,sK1)) = k2_xboole_0(u1_struct_0(sK2),k2_struct_0(sK1)) | v2_struct_0(sK2)),
% 3.73/0.84    inference(resolution,[],[f3446,f328])).
% 3.73/0.84  fof(f3446,plain,(
% 3.73/0.84    ( ! [X3] : (~m1_pre_topc(X3,sK2) | k2_xboole_0(u1_struct_0(X3),k2_struct_0(sK1)) = u1_struct_0(k1_tsep_1(sK2,X3,sK1)) | v2_struct_0(X3)) )),
% 3.73/0.84    inference(forward_demodulation,[],[f3445,f96])).
% 3.73/0.84  fof(f3445,plain,(
% 3.73/0.84    ( ! [X3] : (~m1_pre_topc(X3,sK2) | v2_struct_0(X3) | k2_xboole_0(u1_struct_0(X3),u1_struct_0(sK1)) = u1_struct_0(k1_tsep_1(sK2,X3,sK1))) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f3443,f43])).
% 3.73/0.84  fof(f3443,plain,(
% 3.73/0.84    ( ! [X3] : (~m1_pre_topc(X3,sK2) | v2_struct_0(sK1) | v2_struct_0(X3) | k2_xboole_0(u1_struct_0(X3),u1_struct_0(sK1)) = u1_struct_0(k1_tsep_1(sK2,X3,sK1))) )),
% 3.73/0.84    inference(resolution,[],[f1338,f40])).
% 3.73/0.84  fof(f1338,plain,(
% 3.73/0.84    ( ! [X21,X20] : (~m1_pre_topc(X21,sK2) | ~m1_pre_topc(X20,sK2) | v2_struct_0(X21) | v2_struct_0(X20) | k2_xboole_0(u1_struct_0(X20),u1_struct_0(X21)) = u1_struct_0(k1_tsep_1(sK2,X20,X21))) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f1334,f41])).
% 3.73/0.84  fof(f1334,plain,(
% 3.73/0.84    ( ! [X21,X20] : (v2_struct_0(sK2) | v2_struct_0(X20) | ~m1_pre_topc(X20,sK2) | v2_struct_0(X21) | ~m1_pre_topc(X21,sK2) | k2_xboole_0(u1_struct_0(X20),u1_struct_0(X21)) = u1_struct_0(k1_tsep_1(sK2,X20,X21))) )),
% 3.73/0.84    inference(resolution,[],[f85,f90])).
% 3.73/0.84  fof(f3778,plain,(
% 3.73/0.84    ( ! [X1] : (~r1_xboole_0(X1,k2_struct_0(k1_tsep_1(sK0,sK2,sK1))) | r1_xboole_0(X1,k2_struct_0(sK1))) )),
% 3.73/0.84    inference(backward_demodulation,[],[f1986,f3776])).
% 3.73/0.84  fof(f1986,plain,(
% 3.73/0.84    ( ! [X1] : (~r1_xboole_0(X1,u1_struct_0(k1_tsep_1(sK0,sK2,sK1))) | r1_xboole_0(X1,k2_struct_0(sK1))) )),
% 3.73/0.84    inference(superposition,[],[f74,f1978])).
% 3.73/0.84  fof(f1587,plain,(
% 3.73/0.84    ~r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) | ~l1_struct_0(sK3)),
% 3.73/0.84    inference(subsumption_resolution,[],[f214,f1585])).
% 3.73/0.84  fof(f1585,plain,(
% 3.73/0.84    ~r1_tsep_1(sK3,sK1) | ~l1_struct_0(sK3)),
% 3.73/0.84    inference(subsumption_resolution,[],[f1583,f1477])).
% 3.73/0.84  fof(f1477,plain,(
% 3.73/0.84    ~r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3)) | ~l1_struct_0(sK3)),
% 3.73/0.84    inference(subsumption_resolution,[],[f191,f1476])).
% 3.73/0.84  fof(f1476,plain,(
% 3.73/0.84    ~r1_tsep_1(sK1,sK3) | ~l1_struct_0(sK3)),
% 3.73/0.84    inference(subsumption_resolution,[],[f1475,f37])).
% 3.73/0.84  fof(f37,plain,(
% 3.73/0.84    ~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)),
% 3.73/0.84    inference(cnf_transformation,[],[f17])).
% 3.73/0.84  fof(f1475,plain,(
% 3.73/0.84    ~l1_struct_0(sK3) | r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)),
% 3.73/0.84    inference(duplicate_literal_removal,[],[f1474])).
% 3.73/0.84  fof(f1474,plain,(
% 3.73/0.84    ~l1_struct_0(sK3) | r1_tsep_1(sK3,sK1) | ~l1_struct_0(sK3) | ~r1_tsep_1(sK1,sK3)),
% 3.73/0.84    inference(resolution,[],[f1471,f244])).
% 3.73/0.84  fof(f244,plain,(
% 3.73/0.84    r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3)) | ~l1_struct_0(sK3) | ~r1_tsep_1(sK1,sK3)),
% 3.73/0.84    inference(superposition,[],[f239,f98])).
% 3.73/0.84  fof(f239,plain,(
% 3.73/0.84    ( ! [X0] : (r1_xboole_0(k2_struct_0(sK1),u1_struct_0(X0)) | ~l1_struct_0(X0) | ~r1_tsep_1(sK1,X0)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f238,f89])).
% 3.73/0.84  fof(f238,plain,(
% 3.73/0.84    ( ! [X0] : (~l1_struct_0(X0) | r1_xboole_0(k2_struct_0(sK1),u1_struct_0(X0)) | ~r1_tsep_1(sK1,X0) | ~l1_pre_topc(sK1)) )),
% 3.73/0.84    inference(resolution,[],[f138,f51])).
% 3.73/0.84  fof(f138,plain,(
% 3.73/0.84    ( ! [X1] : (~l1_struct_0(sK1) | ~l1_struct_0(X1) | r1_xboole_0(k2_struct_0(sK1),u1_struct_0(X1)) | ~r1_tsep_1(sK1,X1)) )),
% 3.73/0.84    inference(superposition,[],[f50,f96])).
% 3.73/0.84  fof(f1471,plain,(
% 3.73/0.84    ~r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3)) | ~l1_struct_0(sK3) | r1_tsep_1(sK3,sK1)),
% 3.73/0.84    inference(resolution,[],[f1470,f214])).
% 3.73/0.84  fof(f1470,plain,(
% 3.73/0.84    r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) | ~r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3))),
% 3.73/0.84    inference(subsumption_resolution,[],[f1469,f327])).
% 3.73/0.84  fof(f327,plain,(
% 3.73/0.84    m1_pre_topc(sK1,sK1)),
% 3.73/0.84    inference(resolution,[],[f322,f44])).
% 3.73/0.84  fof(f1469,plain,(
% 3.73/0.84    ~r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3)) | r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) | ~m1_pre_topc(sK1,sK1)),
% 3.73/0.84    inference(subsumption_resolution,[],[f1468,f43])).
% 3.73/0.84  fof(f1468,plain,(
% 3.73/0.84    ~r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3)) | r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK1)),
% 3.73/0.84    inference(duplicate_literal_removal,[],[f1467])).
% 3.73/0.84  fof(f1467,plain,(
% 3.73/0.84    ~r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3)) | r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK1)),
% 3.73/0.84    inference(resolution,[],[f1466,f657])).
% 3.73/0.84  fof(f657,plain,(
% 3.73/0.84    ( ! [X4,X5] : (l1_pre_topc(k1_tsep_1(sK1,X4,X5)) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK1) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK1)) )),
% 3.73/0.84    inference(resolution,[],[f639,f92])).
% 3.73/0.84  fof(f92,plain,(
% 3.73/0.84    ( ! [X0] : (~m1_pre_topc(X0,sK1) | l1_pre_topc(X0)) )),
% 3.73/0.84    inference(resolution,[],[f89,f62])).
% 3.73/0.84  fof(f639,plain,(
% 3.73/0.84    ( ! [X2,X3] : (m1_pre_topc(k1_tsep_1(sK1,X2,X3),sK1) | ~m1_pre_topc(X2,sK1) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK1) | v2_struct_0(X2)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f635,f43])).
% 3.73/0.84  fof(f635,plain,(
% 3.73/0.84    ( ! [X2,X3] : (v2_struct_0(sK1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK1) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK1) | m1_pre_topc(k1_tsep_1(sK1,X2,X3),sK1)) )),
% 3.73/0.84    inference(resolution,[],[f78,f89])).
% 3.73/0.84  fof(f1466,plain,(
% 3.73/0.84    ~l1_pre_topc(k1_tsep_1(sK1,sK1,sK1)) | ~r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3)) | r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))),
% 3.73/0.84    inference(subsumption_resolution,[],[f1465,f51])).
% 3.73/0.84  fof(f1465,plain,(
% 3.73/0.84    ~r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3)) | ~l1_pre_topc(k1_tsep_1(sK1,sK1,sK1)) | ~l1_struct_0(k1_tsep_1(sK1,sK1,sK1)) | r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))),
% 3.73/0.84    inference(resolution,[],[f1245,f894])).
% 3.73/0.84  fof(f894,plain,(
% 3.73/0.84    ~r1_tsep_1(sK3,k1_tsep_1(sK1,sK1,sK1)) | ~l1_struct_0(k1_tsep_1(sK1,sK1,sK1)) | r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))),
% 3.73/0.84    inference(superposition,[],[f275,f866])).
% 3.73/0.84  fof(f866,plain,(
% 3.73/0.84    k2_struct_0(sK1) = u1_struct_0(k1_tsep_1(sK1,sK1,sK1))),
% 3.73/0.84    inference(subsumption_resolution,[],[f865,f43])).
% 3.73/0.84  fof(f865,plain,(
% 3.73/0.84    k2_struct_0(sK1) = u1_struct_0(k1_tsep_1(sK1,sK1,sK1)) | v2_struct_0(sK1)),
% 3.73/0.84    inference(subsumption_resolution,[],[f864,f327])).
% 3.73/0.84  fof(f864,plain,(
% 3.73/0.84    k2_struct_0(sK1) = u1_struct_0(k1_tsep_1(sK1,sK1,sK1)) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1)),
% 3.73/0.84    inference(duplicate_literal_removal,[],[f863])).
% 3.73/0.84  fof(f863,plain,(
% 3.73/0.84    k2_struct_0(sK1) = u1_struct_0(k1_tsep_1(sK1,sK1,sK1)) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(sK1)),
% 3.73/0.84    inference(resolution,[],[f848,f639])).
% 3.73/0.84  fof(f848,plain,(
% 3.73/0.84    ~m1_pre_topc(k1_tsep_1(sK1,sK1,sK1),sK1) | k2_struct_0(sK1) = u1_struct_0(k1_tsep_1(sK1,sK1,sK1))),
% 3.73/0.84    inference(resolution,[],[f846,f513])).
% 3.73/0.84  fof(f513,plain,(
% 3.73/0.84    ( ! [X0] : (~m1_pre_topc(sK1,X0) | ~m1_pre_topc(X0,sK1) | u1_struct_0(X0) = k2_struct_0(sK1)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f507,f501])).
% 3.73/0.84  fof(f501,plain,(
% 3.73/0.84    ( ! [X1] : (r1_tarski(u1_struct_0(X1),k2_struct_0(sK1)) | ~m1_pre_topc(X1,sK1)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f499,f327])).
% 3.73/0.84  fof(f499,plain,(
% 3.73/0.84    ( ! [X1] : (r1_tarski(u1_struct_0(X1),k2_struct_0(sK1)) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(X1,sK1)) )),
% 3.73/0.84    inference(duplicate_literal_removal,[],[f496])).
% 3.73/0.84  fof(f496,plain,(
% 3.73/0.84    ( ! [X1] : (r1_tarski(u1_struct_0(X1),k2_struct_0(sK1)) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(X1,sK1)) )),
% 3.73/0.84    inference(superposition,[],[f234,f96])).
% 3.73/0.84  fof(f234,plain,(
% 3.73/0.84    ( ! [X2,X3] : (r1_tarski(u1_struct_0(X2),u1_struct_0(X3)) | ~m1_pre_topc(X3,sK1) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,sK1)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f230,f105])).
% 3.73/0.84  fof(f105,plain,(
% 3.73/0.84    v2_pre_topc(sK1)),
% 3.73/0.84    inference(resolution,[],[f103,f44])).
% 3.73/0.84  fof(f230,plain,(
% 3.73/0.84    ( ! [X2,X3] : (~v2_pre_topc(sK1) | ~m1_pre_topc(X2,sK1) | ~m1_pre_topc(X3,sK1) | ~m1_pre_topc(X2,X3) | r1_tarski(u1_struct_0(X2),u1_struct_0(X3))) )),
% 3.73/0.84    inference(resolution,[],[f67,f89])).
% 3.73/0.84  fof(f507,plain,(
% 3.73/0.84    ( ! [X0] : (~m1_pre_topc(X0,sK1) | ~m1_pre_topc(sK1,X0) | ~r1_tarski(u1_struct_0(X0),k2_struct_0(sK1)) | u1_struct_0(X0) = k2_struct_0(sK1)) )),
% 3.73/0.84    inference(resolution,[],[f500,f72])).
% 3.73/0.84  fof(f500,plain,(
% 3.73/0.84    ( ! [X1] : (r1_tarski(k2_struct_0(sK1),u1_struct_0(X1)) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(sK1,X1)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f492,f327])).
% 3.73/0.84  fof(f492,plain,(
% 3.73/0.84    ( ! [X1] : (r1_tarski(k2_struct_0(sK1),u1_struct_0(X1)) | ~m1_pre_topc(X1,sK1) | ~m1_pre_topc(sK1,X1) | ~m1_pre_topc(sK1,sK1)) )),
% 3.73/0.84    inference(superposition,[],[f234,f96])).
% 3.73/0.84  fof(f846,plain,(
% 3.73/0.84    m1_pre_topc(sK1,k1_tsep_1(sK1,sK1,sK1))),
% 3.73/0.84    inference(subsumption_resolution,[],[f845,f43])).
% 3.73/0.84  fof(f845,plain,(
% 3.73/0.84    v2_struct_0(sK1) | m1_pre_topc(sK1,k1_tsep_1(sK1,sK1,sK1))),
% 3.73/0.84    inference(resolution,[],[f843,f327])).
% 3.73/0.84  fof(f843,plain,(
% 3.73/0.84    ( ! [X3] : (~m1_pre_topc(X3,sK1) | v2_struct_0(X3) | m1_pre_topc(X3,k1_tsep_1(sK1,X3,sK1))) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f842,f43])).
% 3.73/0.84  fof(f842,plain,(
% 3.73/0.84    ( ! [X3] : (~m1_pre_topc(X3,sK1) | v2_struct_0(sK1) | v2_struct_0(X3) | m1_pre_topc(X3,k1_tsep_1(sK1,X3,sK1))) )),
% 3.73/0.84    inference(resolution,[],[f790,f327])).
% 3.73/0.84  fof(f790,plain,(
% 3.73/0.84    ( ! [X19,X18] : (~m1_pre_topc(X19,sK1) | ~m1_pre_topc(X18,sK1) | v2_struct_0(X19) | v2_struct_0(X18) | m1_pre_topc(X18,k1_tsep_1(sK1,X18,X19))) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f789,f43])).
% 3.73/0.84  fof(f789,plain,(
% 3.73/0.84    ( ! [X19,X18] : (v2_struct_0(sK1) | v2_struct_0(X18) | ~m1_pre_topc(X18,sK1) | v2_struct_0(X19) | ~m1_pre_topc(X19,sK1) | m1_pre_topc(X18,k1_tsep_1(sK1,X18,X19))) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f780,f105])).
% 3.73/0.84  fof(f780,plain,(
% 3.73/0.84    ( ! [X19,X18] : (~v2_pre_topc(sK1) | v2_struct_0(sK1) | v2_struct_0(X18) | ~m1_pre_topc(X18,sK1) | v2_struct_0(X19) | ~m1_pre_topc(X19,sK1) | m1_pre_topc(X18,k1_tsep_1(sK1,X18,X19))) )),
% 3.73/0.84    inference(resolution,[],[f63,f89])).
% 3.73/0.84  fof(f1245,plain,(
% 3.73/0.84    r1_tsep_1(sK3,k1_tsep_1(sK1,sK1,sK1)) | ~r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3)) | ~l1_pre_topc(k1_tsep_1(sK1,sK1,sK1))),
% 3.73/0.84    inference(subsumption_resolution,[],[f1244,f51])).
% 3.73/0.84  fof(f1244,plain,(
% 3.73/0.84    ~l1_struct_0(k1_tsep_1(sK1,sK1,sK1)) | ~r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3)) | r1_tsep_1(sK3,k1_tsep_1(sK1,sK1,sK1)) | ~l1_pre_topc(k1_tsep_1(sK1,sK1,sK1))),
% 3.73/0.84    inference(resolution,[],[f883,f117])).
% 3.73/0.84  fof(f883,plain,(
% 3.73/0.84    r1_tsep_1(k1_tsep_1(sK1,sK1,sK1),sK3) | ~l1_struct_0(k1_tsep_1(sK1,sK1,sK1)) | ~r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3))),
% 3.73/0.84    inference(superposition,[],[f224,f866])).
% 3.73/0.84  fof(f224,plain,(
% 3.73/0.84    ( ! [X0] : (~r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK3)) | ~l1_struct_0(X0) | r1_tsep_1(X0,sK3)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f223,f88])).
% 3.73/0.84  fof(f223,plain,(
% 3.73/0.84    ( ! [X0] : (~r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK3)) | ~l1_struct_0(X0) | r1_tsep_1(X0,sK3) | ~l1_pre_topc(sK3)) )),
% 3.73/0.84    inference(resolution,[],[f133,f51])).
% 3.73/0.84  fof(f133,plain,(
% 3.73/0.84    ( ! [X3] : (~l1_struct_0(sK3) | ~r1_xboole_0(u1_struct_0(X3),k2_struct_0(sK3)) | ~l1_struct_0(X3) | r1_tsep_1(X3,sK3)) )),
% 3.73/0.84    inference(superposition,[],[f49,f98])).
% 3.73/0.84  fof(f191,plain,(
% 3.73/0.84    ~r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3)) | ~l1_struct_0(sK3) | r1_tsep_1(sK1,sK3)),
% 3.73/0.84    inference(superposition,[],[f187,f98])).
% 3.73/0.84  fof(f187,plain,(
% 3.73/0.84    ( ! [X0] : (~r1_xboole_0(k2_struct_0(sK1),u1_struct_0(X0)) | ~l1_struct_0(X0) | r1_tsep_1(sK1,X0)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f186,f89])).
% 3.73/0.84  fof(f186,plain,(
% 3.73/0.84    ( ! [X0] : (~l1_struct_0(X0) | ~r1_xboole_0(k2_struct_0(sK1),u1_struct_0(X0)) | r1_tsep_1(sK1,X0) | ~l1_pre_topc(sK1)) )),
% 3.73/0.84    inference(resolution,[],[f127,f51])).
% 3.73/0.84  fof(f127,plain,(
% 3.73/0.84    ( ! [X1] : (~l1_struct_0(sK1) | ~l1_struct_0(X1) | ~r1_xboole_0(k2_struct_0(sK1),u1_struct_0(X1)) | r1_tsep_1(sK1,X1)) )),
% 3.73/0.84    inference(superposition,[],[f49,f96])).
% 3.73/0.84  fof(f1583,plain,(
% 3.73/0.84    r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3)) | ~l1_struct_0(sK3) | ~r1_tsep_1(sK3,sK1)),
% 3.73/0.84    inference(resolution,[],[f1581,f297])).
% 3.73/0.84  fof(f297,plain,(
% 3.73/0.84    r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) | ~l1_struct_0(sK3) | ~r1_tsep_1(sK3,sK1)),
% 3.73/0.84    inference(superposition,[],[f292,f98])).
% 3.73/0.84  fof(f292,plain,(
% 3.73/0.84    ( ! [X0] : (r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK1)) | ~l1_struct_0(X0) | ~r1_tsep_1(X0,sK1)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f291,f89])).
% 3.73/0.84  fof(f291,plain,(
% 3.73/0.84    ( ! [X0] : (r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK1)) | ~l1_struct_0(X0) | ~r1_tsep_1(X0,sK1) | ~l1_pre_topc(sK1)) )),
% 3.73/0.84    inference(resolution,[],[f142,f51])).
% 3.73/0.84  fof(f142,plain,(
% 3.73/0.84    ( ! [X1] : (~l1_struct_0(sK1) | r1_xboole_0(u1_struct_0(X1),k2_struct_0(sK1)) | ~l1_struct_0(X1) | ~r1_tsep_1(X1,sK1)) )),
% 3.73/0.84    inference(superposition,[],[f50,f96])).
% 3.73/0.84  fof(f1581,plain,(
% 3.73/0.84    ~r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) | r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3))),
% 3.73/0.84    inference(subsumption_resolution,[],[f1580,f326])).
% 3.73/0.84  fof(f326,plain,(
% 3.73/0.84    m1_pre_topc(sK3,sK3)),
% 3.73/0.84    inference(resolution,[],[f322,f39])).
% 3.73/0.84  fof(f1580,plain,(
% 3.73/0.84    ~r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) | r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3)) | ~m1_pre_topc(sK3,sK3)),
% 3.73/0.84    inference(subsumption_resolution,[],[f1579,f38])).
% 3.73/0.84  fof(f38,plain,(
% 3.73/0.84    ~v2_struct_0(sK3)),
% 3.73/0.84    inference(cnf_transformation,[],[f17])).
% 3.73/0.84  fof(f1579,plain,(
% 3.73/0.84    ~r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) | r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3)) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK3)),
% 3.73/0.84    inference(duplicate_literal_removal,[],[f1578])).
% 3.73/0.84  fof(f1578,plain,(
% 3.73/0.84    ~r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) | r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3)) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK3) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK3)),
% 3.73/0.84    inference(resolution,[],[f1577,f683])).
% 3.73/0.84  fof(f683,plain,(
% 3.73/0.84    ( ! [X4,X5] : (l1_pre_topc(k1_tsep_1(sK3,X4,X5)) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK3) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK3)) )),
% 3.73/0.84    inference(resolution,[],[f641,f91])).
% 3.73/0.84  fof(f91,plain,(
% 3.73/0.84    ( ! [X0] : (~m1_pre_topc(X0,sK3) | l1_pre_topc(X0)) )),
% 3.73/0.84    inference(resolution,[],[f88,f62])).
% 3.73/0.84  fof(f641,plain,(
% 3.73/0.84    ( ! [X6,X7] : (m1_pre_topc(k1_tsep_1(sK3,X6,X7),sK3) | ~m1_pre_topc(X6,sK3) | v2_struct_0(X7) | ~m1_pre_topc(X7,sK3) | v2_struct_0(X6)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f637,f38])).
% 3.73/0.84  fof(f637,plain,(
% 3.73/0.84    ( ! [X6,X7] : (v2_struct_0(sK3) | v2_struct_0(X6) | ~m1_pre_topc(X6,sK3) | v2_struct_0(X7) | ~m1_pre_topc(X7,sK3) | m1_pre_topc(k1_tsep_1(sK3,X6,X7),sK3)) )),
% 3.73/0.84    inference(resolution,[],[f78,f88])).
% 3.73/0.84  fof(f1577,plain,(
% 3.73/0.84    ~l1_pre_topc(k1_tsep_1(sK3,sK3,sK3)) | ~r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) | r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3))),
% 3.73/0.84    inference(subsumption_resolution,[],[f1576,f51])).
% 3.73/0.84  fof(f1576,plain,(
% 3.73/0.84    ~r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) | ~l1_pre_topc(k1_tsep_1(sK3,sK3,sK3)) | ~l1_struct_0(k1_tsep_1(sK3,sK3,sK3)) | r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3))),
% 3.73/0.84    inference(resolution,[],[f1371,f1198])).
% 3.73/0.84  fof(f1198,plain,(
% 3.73/0.84    ~r1_tsep_1(sK1,k1_tsep_1(sK3,sK3,sK3)) | ~l1_struct_0(k1_tsep_1(sK3,sK3,sK3)) | r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3))),
% 3.73/0.84    inference(superposition,[],[f239,f1171])).
% 3.73/0.84  fof(f1171,plain,(
% 3.73/0.84    k2_struct_0(sK3) = u1_struct_0(k1_tsep_1(sK3,sK3,sK3))),
% 3.73/0.84    inference(subsumption_resolution,[],[f1170,f38])).
% 3.73/0.84  fof(f1170,plain,(
% 3.73/0.84    k2_struct_0(sK3) = u1_struct_0(k1_tsep_1(sK3,sK3,sK3)) | v2_struct_0(sK3)),
% 3.73/0.84    inference(subsumption_resolution,[],[f1169,f326])).
% 3.73/0.84  fof(f1169,plain,(
% 3.73/0.84    k2_struct_0(sK3) = u1_struct_0(k1_tsep_1(sK3,sK3,sK3)) | ~m1_pre_topc(sK3,sK3) | v2_struct_0(sK3)),
% 3.73/0.84    inference(duplicate_literal_removal,[],[f1168])).
% 3.73/0.84  fof(f1168,plain,(
% 3.73/0.84    k2_struct_0(sK3) = u1_struct_0(k1_tsep_1(sK3,sK3,sK3)) | ~m1_pre_topc(sK3,sK3) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK3) | v2_struct_0(sK3)),
% 3.73/0.84    inference(resolution,[],[f1133,f641])).
% 3.73/0.84  fof(f1133,plain,(
% 3.73/0.84    ~m1_pre_topc(k1_tsep_1(sK3,sK3,sK3),sK3) | k2_struct_0(sK3) = u1_struct_0(k1_tsep_1(sK3,sK3,sK3))),
% 3.73/0.84    inference(resolution,[],[f1131,f605])).
% 3.73/0.84  fof(f605,plain,(
% 3.73/0.84    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~m1_pre_topc(X0,sK3) | u1_struct_0(X0) = k2_struct_0(sK3)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f599,f593])).
% 3.73/0.84  fof(f593,plain,(
% 3.73/0.84    ( ! [X3] : (r1_tarski(u1_struct_0(X3),k2_struct_0(sK3)) | ~m1_pre_topc(X3,sK3)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f591,f326])).
% 3.73/0.84  fof(f591,plain,(
% 3.73/0.84    ( ! [X3] : (r1_tarski(u1_struct_0(X3),k2_struct_0(sK3)) | ~m1_pre_topc(sK3,sK3) | ~m1_pre_topc(X3,sK3)) )),
% 3.73/0.84    inference(duplicate_literal_removal,[],[f590])).
% 3.73/0.84  fof(f590,plain,(
% 3.73/0.84    ( ! [X3] : (r1_tarski(u1_struct_0(X3),k2_struct_0(sK3)) | ~m1_pre_topc(sK3,sK3) | ~m1_pre_topc(X3,sK3) | ~m1_pre_topc(X3,sK3)) )),
% 3.73/0.84    inference(superposition,[],[f236,f98])).
% 3.73/0.84  fof(f236,plain,(
% 3.73/0.84    ( ! [X6,X7] : (r1_tarski(u1_struct_0(X6),u1_struct_0(X7)) | ~m1_pre_topc(X7,sK3) | ~m1_pre_topc(X6,X7) | ~m1_pre_topc(X6,sK3)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f232,f104])).
% 3.73/0.84  fof(f104,plain,(
% 3.73/0.84    v2_pre_topc(sK3)),
% 3.73/0.84    inference(resolution,[],[f103,f39])).
% 3.73/0.84  fof(f232,plain,(
% 3.73/0.84    ( ! [X6,X7] : (~v2_pre_topc(sK3) | ~m1_pre_topc(X6,sK3) | ~m1_pre_topc(X7,sK3) | ~m1_pre_topc(X6,X7) | r1_tarski(u1_struct_0(X6),u1_struct_0(X7))) )),
% 3.73/0.84    inference(resolution,[],[f67,f88])).
% 3.73/0.84  fof(f599,plain,(
% 3.73/0.84    ( ! [X0] : (~m1_pre_topc(X0,sK3) | ~m1_pre_topc(sK3,X0) | ~r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) | u1_struct_0(X0) = k2_struct_0(sK3)) )),
% 3.73/0.84    inference(resolution,[],[f592,f72])).
% 3.73/0.84  fof(f592,plain,(
% 3.73/0.84    ( ! [X3] : (r1_tarski(k2_struct_0(sK3),u1_struct_0(X3)) | ~m1_pre_topc(X3,sK3) | ~m1_pre_topc(sK3,X3)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f586,f326])).
% 3.73/0.84  fof(f586,plain,(
% 3.73/0.84    ( ! [X3] : (r1_tarski(k2_struct_0(sK3),u1_struct_0(X3)) | ~m1_pre_topc(X3,sK3) | ~m1_pre_topc(sK3,X3) | ~m1_pre_topc(sK3,sK3)) )),
% 3.73/0.84    inference(superposition,[],[f236,f98])).
% 3.73/0.84  fof(f1131,plain,(
% 3.73/0.84    m1_pre_topc(sK3,k1_tsep_1(sK3,sK3,sK3))),
% 3.73/0.84    inference(subsumption_resolution,[],[f1130,f38])).
% 3.73/0.84  fof(f1130,plain,(
% 3.73/0.84    v2_struct_0(sK3) | m1_pre_topc(sK3,k1_tsep_1(sK3,sK3,sK3))),
% 3.73/0.84    inference(resolution,[],[f1128,f326])).
% 3.73/0.84  fof(f1128,plain,(
% 3.73/0.84    ( ! [X3] : (~m1_pre_topc(X3,sK3) | v2_struct_0(X3) | m1_pre_topc(X3,k1_tsep_1(sK3,X3,sK3))) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f1127,f38])).
% 3.73/0.84  fof(f1127,plain,(
% 3.73/0.84    ( ! [X3] : (~m1_pre_topc(X3,sK3) | v2_struct_0(sK3) | v2_struct_0(X3) | m1_pre_topc(X3,k1_tsep_1(sK3,X3,sK3))) )),
% 3.73/0.84    inference(resolution,[],[f794,f326])).
% 3.73/0.84  fof(f794,plain,(
% 3.73/0.84    ( ! [X23,X22] : (~m1_pre_topc(X23,sK3) | ~m1_pre_topc(X22,sK3) | v2_struct_0(X23) | v2_struct_0(X22) | m1_pre_topc(X22,k1_tsep_1(sK3,X22,X23))) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f793,f38])).
% 3.73/0.84  fof(f793,plain,(
% 3.73/0.84    ( ! [X23,X22] : (v2_struct_0(sK3) | v2_struct_0(X22) | ~m1_pre_topc(X22,sK3) | v2_struct_0(X23) | ~m1_pre_topc(X23,sK3) | m1_pre_topc(X22,k1_tsep_1(sK3,X22,X23))) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f782,f104])).
% 3.73/0.84  fof(f782,plain,(
% 3.73/0.84    ( ! [X23,X22] : (~v2_pre_topc(sK3) | v2_struct_0(sK3) | v2_struct_0(X22) | ~m1_pre_topc(X22,sK3) | v2_struct_0(X23) | ~m1_pre_topc(X23,sK3) | m1_pre_topc(X22,k1_tsep_1(sK3,X22,X23))) )),
% 3.73/0.84    inference(resolution,[],[f63,f88])).
% 3.73/0.84  fof(f1371,plain,(
% 3.73/0.84    r1_tsep_1(sK1,k1_tsep_1(sK3,sK3,sK3)) | ~r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) | ~l1_pre_topc(k1_tsep_1(sK3,sK3,sK3))),
% 3.73/0.84    inference(subsumption_resolution,[],[f1370,f51])).
% 3.73/0.84  fof(f1370,plain,(
% 3.73/0.84    ~l1_struct_0(k1_tsep_1(sK3,sK3,sK3)) | ~r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) | r1_tsep_1(sK1,k1_tsep_1(sK3,sK3,sK3)) | ~l1_pre_topc(k1_tsep_1(sK3,sK3,sK3))),
% 3.73/0.84    inference(resolution,[],[f1187,f115])).
% 3.73/0.84  fof(f115,plain,(
% 3.73/0.84    ( ! [X1] : (~r1_tsep_1(X1,sK1) | r1_tsep_1(sK1,X1) | ~l1_pre_topc(X1)) )),
% 3.73/0.84    inference(resolution,[],[f113,f89])).
% 3.73/0.84  fof(f1187,plain,(
% 3.73/0.84    r1_tsep_1(k1_tsep_1(sK3,sK3,sK3),sK1) | ~l1_struct_0(k1_tsep_1(sK3,sK3,sK3)) | ~r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1))),
% 3.73/0.84    inference(superposition,[],[f210,f1171])).
% 3.73/0.84  fof(f210,plain,(
% 3.73/0.84    ( ! [X0] : (~r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK1)) | ~l1_struct_0(X0) | r1_tsep_1(X0,sK1)) )),
% 3.73/0.84    inference(subsumption_resolution,[],[f209,f89])).
% 3.73/0.84  fof(f209,plain,(
% 3.73/0.84    ( ! [X0] : (~r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK1)) | ~l1_struct_0(X0) | r1_tsep_1(X0,sK1) | ~l1_pre_topc(sK1)) )),
% 3.73/0.84    inference(resolution,[],[f131,f51])).
% 3.73/0.84  fof(f131,plain,(
% 3.73/0.84    ( ! [X1] : (~l1_struct_0(sK1) | ~r1_xboole_0(u1_struct_0(X1),k2_struct_0(sK1)) | ~l1_struct_0(X1) | r1_tsep_1(X1,sK1)) )),
% 3.73/0.84    inference(superposition,[],[f49,f96])).
% 3.73/0.84  fof(f214,plain,(
% 3.73/0.84    ~r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK1)) | ~l1_struct_0(sK3) | r1_tsep_1(sK3,sK1)),
% 3.73/0.84    inference(superposition,[],[f210,f98])).
% 3.73/0.84  % SZS output end Proof for theBenchmark
% 3.73/0.84  % (11119)------------------------------
% 3.73/0.84  % (11119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.73/0.84  % (11119)Termination reason: Refutation
% 3.73/0.84  
% 3.73/0.84  % (11119)Memory used [KB]: 4733
% 3.73/0.84  % (11119)Time elapsed: 0.400 s
% 3.73/0.84  % (11119)------------------------------
% 3.73/0.84  % (11119)------------------------------
% 3.73/0.86  % (11099)Success in time 0.508 s
%------------------------------------------------------------------------------
