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
% DateTime   : Thu Dec  3 13:18:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 305 expanded)
%              Number of leaves         :    4 (  52 expanded)
%              Depth                    :   32
%              Number of atoms          :  485 (3075 expanded)
%              Number of equality atoms :    2 (   6 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f120,plain,(
    $false ),
    inference(subsumption_resolution,[],[f119,f23])).

fof(f23,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                      & m1_pre_topc(X2,X3) )
                    | ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
                      & m1_pre_topc(X1,X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                      & m1_pre_topc(X2,X3) )
                    | ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
                      & m1_pre_topc(X1,X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
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
                   => ( ~ r1_tsep_1(X1,X2)
                     => ( ( m1_pre_topc(X2,X3)
                         => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) )
                        & ( m1_pre_topc(X1,X3)
                         => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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
                 => ( ~ r1_tsep_1(X1,X2)
                   => ( ( m1_pre_topc(X2,X3)
                       => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) )
                      & ( m1_pre_topc(X1,X3)
                       => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tmap_1)).

fof(f119,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f118,f18])).

fof(f18,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f118,plain,
    ( r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f117,f90])).

fof(f90,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f89,f14])).

fof(f14,plain,
    ( m1_pre_topc(sK2,sK3)
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f89,plain,
    ( ~ m1_pre_topc(sK1,sK3)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f88,f23])).

fof(f88,plain,
    ( ~ m1_pre_topc(sK1,sK3)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f87,f18])).

fof(f87,plain,
    ( ~ m1_pre_topc(sK1,sK3)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f86,f56])).

fof(f56,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f54,f20])).

fof(f20,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_pre_topc(X0,X0) ) ),
    inference(subsumption_resolution,[],[f53,f24])).

fof(f24,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_pre_topc(X0,X0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f52,f25])).

fof(f25,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X4,X3] :
      ( ~ l1_pre_topc(X3)
      | ~ m1_pre_topc(X4,X3)
      | m1_pre_topc(X4,X4)
      | ~ v2_pre_topc(X3) ) ),
    inference(duplicate_literal_removal,[],[f51])).

fof(f51,plain,(
    ! [X4,X3] :
      ( ~ l1_pre_topc(X3)
      | ~ m1_pre_topc(X4,X3)
      | ~ m1_pre_topc(X4,X3)
      | m1_pre_topc(X4,X4)
      | ~ v2_pre_topc(X3) ) ),
    inference(resolution,[],[f28,f32])).

fof(f32,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X1,X2)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
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
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f86,plain,
    ( ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f85,f17])).

fof(f17,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f85,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f84,f16])).

fof(f16,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f84,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f83,f20])).

fof(f83,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f82,f19])).

fof(f19,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f82,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f81,f22])).

fof(f22,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f81,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f80,f21])).

fof(f21,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f80,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f79,f25])).

fof(f79,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f65,f24])).

fof(f65,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f62])).

fof(f62,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(resolution,[],[f26,f12])).

fof(f12,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2))
    | m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X0)
      | ~ m1_pre_topc(X1,X3)
      | ~ m1_pre_topc(X2,X4)
      | r1_tsep_1(X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                      | r1_tsep_1(X1,X2)
                      | ~ m1_pre_topc(X2,X4)
                      | ~ m1_pre_topc(X1,X3)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                      | r1_tsep_1(X1,X2)
                      | ~ m1_pre_topc(X2,X4)
                      | ~ m1_pre_topc(X1,X3)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X2,X4)
                          & m1_pre_topc(X1,X3) )
                       => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                          | r1_tsep_1(X1,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tmap_1)).

fof(f117,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f116,f57])).

fof(f57,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(resolution,[],[f54,f22])).

fof(f116,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f115,f17])).

fof(f115,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f114,f16])).

fof(f114,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f113,f20])).

fof(f113,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f112,f19])).

fof(f112,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f111,f22])).

fof(f111,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f110,f21])).

fof(f110,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f109,f25])).

fof(f109,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f108,f24])).

fof(f108,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK2,sK3)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f78,f26])).

fof(f78,plain,(
    ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f77,f15])).

fof(f15,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f77,plain,
    ( ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f76,f23])).

fof(f76,plain,
    ( ~ m1_pre_topc(sK1,sK3)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f75,f18])).

fof(f75,plain,
    ( ~ m1_pre_topc(sK1,sK3)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f74,f56])).

fof(f74,plain,
    ( ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f73,f17])).

fof(f73,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f72,f16])).

fof(f72,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f71,f20])).

fof(f71,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f70,f19])).

fof(f70,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f69,f22])).

fof(f69,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f68,f21])).

fof(f68,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f67,f25])).

fof(f67,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f66,f24])).

fof(f66,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(duplicate_literal_removal,[],[f61])).

fof(f61,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK2)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(resolution,[],[f26,f13])).

fof(f13,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:20:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (22645)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.48  % (22645)Refutation not found, incomplete strategy% (22645)------------------------------
% 0.20/0.48  % (22645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (22639)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.48  % (22655)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.48  % (22653)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.49  % (22647)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (22653)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(subsumption_resolution,[],[f119,f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ~v2_struct_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) & m1_pre_topc(X2,X3)) | (~m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f6])).
% 0.20/0.49  fof(f6,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) & m1_pre_topc(X2,X3)) | (~m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((m1_pre_topc(X2,X3) => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))) & (m1_pre_topc(X1,X3) => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)))))))))),
% 0.20/0.49    inference(negated_conjecture,[],[f4])).
% 0.20/0.49  fof(f4,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((m1_pre_topc(X2,X3) => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))) & (m1_pre_topc(X1,X3) => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)))))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tmap_1)).
% 0.20/0.49  fof(f119,plain,(
% 0.20/0.49    v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f118,f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ~r1_tsep_1(sK1,sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    r1_tsep_1(sK1,sK2) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f117,f90])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    m1_pre_topc(sK2,sK3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f89,f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    m1_pre_topc(sK2,sK3) | m1_pre_topc(sK1,sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    ~m1_pre_topc(sK1,sK3) | m1_pre_topc(sK2,sK3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f88,f23])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    ~m1_pre_topc(sK1,sK3) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f87,f18])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    ~m1_pre_topc(sK1,sK3) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f86,f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    m1_pre_topc(sK2,sK2)),
% 0.20/0.49    inference(resolution,[],[f54,f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    m1_pre_topc(sK2,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_pre_topc(X0,X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f53,f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    v2_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_pre_topc(X0,X0) | ~v2_pre_topc(sK0)) )),
% 0.20/0.49    inference(resolution,[],[f52,f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    l1_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X4,X3] : (~l1_pre_topc(X3) | ~m1_pre_topc(X4,X3) | m1_pre_topc(X4,X4) | ~v2_pre_topc(X3)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X4,X3] : (~l1_pre_topc(X3) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(X4,X3) | m1_pre_topc(X4,X4) | ~v2_pre_topc(X3)) )),
% 0.20/0.49    inference(resolution,[],[f28,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.49    inference(equality_resolution,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | m1_pre_topc(X1,X2) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f85,f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    m1_pre_topc(sK3,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f84,f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ~v2_struct_0(sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f83,f20])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f82,f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ~v2_struct_0(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f81,f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    m1_pre_topc(sK1,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f80,f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ~v2_struct_0(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f79,f25])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f65,f24])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK3)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f62])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | m1_pre_topc(sK2,sK3)),
% 0.20/0.49    inference(resolution,[],[f26,f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2)) | m1_pre_topc(sK2,sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X3,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X4) | ~m1_pre_topc(X4,X0) | ~m1_pre_topc(X1,X3) | ~m1_pre_topc(X2,X4) | r1_tsep_1(X1,X2) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X4) | ~m1_pre_topc(X1,X3) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f8])).
% 0.20/0.49  fof(f8,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X4) | ~m1_pre_topc(X1,X3))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X2,X4) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | r1_tsep_1(X1,X2))))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tmap_1)).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    ~m1_pre_topc(sK2,sK3) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f116,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    m1_pre_topc(sK1,sK1)),
% 0.20/0.49    inference(resolution,[],[f54,f22])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK2,sK3) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f115,f17])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK2,sK3) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f114,f16])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK2,sK3) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f113,f20])).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK2,sK3) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f112,f19])).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK2,sK3) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f111,f22])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK2,sK3) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f110,f21])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK2,sK3) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f109,f25])).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK2,sK3) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f108,f24])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK2,sK3) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f107])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(sK2,sK3) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0)),
% 0.20/0.49    inference(resolution,[],[f78,f26])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.20/0.49    inference(subsumption_resolution,[],[f77,f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) | m1_pre_topc(sK1,sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.20/0.49    inference(subsumption_resolution,[],[f76,f23])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ~m1_pre_topc(sK1,sK3) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.20/0.49    inference(subsumption_resolution,[],[f75,f18])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ~m1_pre_topc(sK1,sK3) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.20/0.49    inference(subsumption_resolution,[],[f74,f56])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.20/0.49    inference(subsumption_resolution,[],[f73,f17])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.20/0.49    inference(subsumption_resolution,[],[f72,f16])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.20/0.49    inference(subsumption_resolution,[],[f71,f20])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.20/0.49    inference(subsumption_resolution,[],[f70,f19])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.20/0.49    inference(subsumption_resolution,[],[f69,f22])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.20/0.49    inference(subsumption_resolution,[],[f68,f21])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.20/0.49    inference(subsumption_resolution,[],[f67,f25])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.20/0.49    inference(subsumption_resolution,[],[f66,f24])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f61])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK2) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.20/0.49    inference(resolution,[],[f26,f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (22653)------------------------------
% 0.20/0.49  % (22653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (22653)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (22653)Memory used [KB]: 1663
% 0.20/0.49  % (22653)Time elapsed: 0.072 s
% 0.20/0.49  % (22653)------------------------------
% 0.20/0.49  % (22653)------------------------------
% 0.20/0.49  % (22647)Refutation not found, incomplete strategy% (22647)------------------------------
% 0.20/0.49  % (22647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (22647)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (22647)Memory used [KB]: 6140
% 0.20/0.49  % (22647)Time elapsed: 0.005 s
% 0.20/0.49  % (22647)------------------------------
% 0.20/0.49  % (22647)------------------------------
% 0.20/0.49  % (22633)Success in time 0.135 s
%------------------------------------------------------------------------------
