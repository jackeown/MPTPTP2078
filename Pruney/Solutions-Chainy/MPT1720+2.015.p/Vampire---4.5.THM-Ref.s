%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 915 expanded)
%              Number of leaves         :    8 ( 156 expanded)
%              Depth                    :   29
%              Number of atoms          :  749 (7881 expanded)
%              Number of equality atoms :   59 ( 151 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8580,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8579,f5688])).

fof(f5688,plain,(
    r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f5687,f1097])).

fof(f1097,plain,(
    u1_struct_0(sK2) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f1096,f1002])).

fof(f1002,plain,(
    u1_struct_0(sK2) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) ),
    inference(resolution,[],[f959,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f959,plain,(
    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) ),
    inference(resolution,[],[f956,f766])).

fof(f766,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) ),
    inference(resolution,[],[f734,f31])).

fof(f31,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
                   => ( ( m1_pre_topc(X3,X2)
                        & m1_pre_topc(X1,X2) )
                     => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
                 => ( ( m1_pre_topc(X3,X2)
                      & m1_pre_topc(X1,X2) )
                   => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tmap_1)).

fof(f734,plain,(
    ! [X10] :
      ( ~ m1_pre_topc(X10,sK0)
      | ~ m1_pre_topc(sK2,X10)
      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X10)) ) ),
    inference(resolution,[],[f172,f31])).

fof(f172,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ m1_pre_topc(X1,sK0)
      | ~ m1_pre_topc(X0,X1)
      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f166,f36])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_pre_topc(X1,sK0)
      | ~ m1_pre_topc(X0,X1)
      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ) ),
    inference(resolution,[],[f35,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f956,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(subsumption_resolution,[],[f955,f798])).

fof(f798,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) ),
    inference(subsumption_resolution,[],[f793,f30])).

fof(f30,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f793,plain,
    ( v2_struct_0(sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) ),
    inference(resolution,[],[f181,f31])).

fof(f181,plain,(
    ! [X12] :
      ( ~ m1_pre_topc(X12,sK0)
      | v2_struct_0(X12)
      | k1_tsep_1(sK0,X12,X12) = g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12)) ) ),
    inference(subsumption_resolution,[],[f180,f36])).

fof(f180,plain,(
    ! [X12] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(X12)
      | ~ m1_pre_topc(X12,sK0)
      | k1_tsep_1(sK0,X12,X12) = g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12)) ) ),
    inference(subsumption_resolution,[],[f171,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f171,plain,(
    ! [X12] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X12)
      | ~ m1_pre_topc(X12,sK0)
      | k1_tsep_1(sK0,X12,X12) = g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12)) ) ),
    inference(resolution,[],[f35,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tmap_1)).

fof(f955,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k1_tsep_1(sK0,sK2,sK2)
    | m1_pre_topc(sK2,sK2) ),
    inference(subsumption_resolution,[],[f949,f30])).

fof(f949,plain,
    ( v2_struct_0(sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k1_tsep_1(sK0,sK2,sK2)
    | m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f836,f31])).

fof(f836,plain,(
    ! [X10] :
      ( ~ m1_pre_topc(X10,sK0)
      | v2_struct_0(X10)
      | k1_tsep_1(sK0,sK2,X10) != g1_pre_topc(u1_struct_0(X10),u1_pre_topc(X10))
      | m1_pre_topc(sK2,X10) ) ),
    inference(subsumption_resolution,[],[f831,f30])).

fof(f831,plain,(
    ! [X10] :
      ( v2_struct_0(sK2)
      | v2_struct_0(X10)
      | ~ m1_pre_topc(X10,sK0)
      | k1_tsep_1(sK0,sK2,X10) != g1_pre_topc(u1_struct_0(X10),u1_pre_topc(X10))
      | m1_pre_topc(sK2,X10) ) ),
    inference(resolution,[],[f177,f31])).

fof(f177,plain,(
    ! [X8,X9] :
      ( ~ m1_pre_topc(X8,sK0)
      | v2_struct_0(X8)
      | v2_struct_0(X9)
      | ~ m1_pre_topc(X9,sK0)
      | k1_tsep_1(sK0,X8,X9) != g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9))
      | m1_pre_topc(X8,X9) ) ),
    inference(subsumption_resolution,[],[f176,f36])).

fof(f176,plain,(
    ! [X8,X9] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(X8,sK0)
      | v2_struct_0(X9)
      | ~ m1_pre_topc(X9,sK0)
      | k1_tsep_1(sK0,X8,X9) != g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9))
      | m1_pre_topc(X8,X9) ) ),
    inference(subsumption_resolution,[],[f169,f34])).

fof(f169,plain,(
    ! [X8,X9] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(X8,sK0)
      | v2_struct_0(X9)
      | ~ m1_pre_topc(X9,sK0)
      | k1_tsep_1(sK0,X8,X9) != g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9))
      | m1_pre_topc(X8,X9) ) ),
    inference(resolution,[],[f35,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | m1_pre_topc(X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
              <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
              <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
             => ( m1_pre_topc(X1,X2)
              <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tsep_1)).

fof(f1096,plain,(
    k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f1095,f1089])).

fof(f1089,plain,(
    m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f1088,f31])).

fof(f1088,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0) ),
    inference(subsumption_resolution,[],[f1087,f30])).

fof(f1087,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0) ),
    inference(subsumption_resolution,[],[f1086,f36])).

fof(f1086,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0) ),
    inference(subsumption_resolution,[],[f1080,f34])).

fof(f1080,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0) ),
    inference(duplicate_literal_removal,[],[f1074])).

fof(f1074,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0) ),
    inference(superposition,[],[f48,f1064])).

fof(f1064,plain,(
    k1_tsep_1(sK0,sK2,sK2) = k1_tsep_1(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f798,f1063])).

fof(f1063,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f1062,f27])).

fof(f27,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f1062,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK1,sK2)
    | ~ m1_pre_topc(sK1,sK2) ),
    inference(subsumption_resolution,[],[f1058,f30])).

fof(f1058,plain,
    ( v2_struct_0(sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK1,sK2)
    | ~ m1_pre_topc(sK1,sK2) ),
    inference(resolution,[],[f867,f31])).

fof(f867,plain,(
    ! [X9] :
      ( ~ m1_pre_topc(X9,sK0)
      | v2_struct_0(X9)
      | g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)) = k1_tsep_1(sK0,sK1,X9)
      | ~ m1_pre_topc(sK1,X9) ) ),
    inference(subsumption_resolution,[],[f862,f32])).

fof(f32,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f862,plain,(
    ! [X9] :
      ( v2_struct_0(sK1)
      | v2_struct_0(X9)
      | ~ m1_pre_topc(X9,sK0)
      | g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)) = k1_tsep_1(sK0,sK1,X9)
      | ~ m1_pre_topc(sK1,X9) ) ),
    inference(resolution,[],[f179,f33])).

fof(f33,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f179,plain,(
    ! [X10,X11] :
      ( ~ m1_pre_topc(X10,sK0)
      | v2_struct_0(X10)
      | v2_struct_0(X11)
      | ~ m1_pre_topc(X11,sK0)
      | k1_tsep_1(sK0,X10,X11) = g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11))
      | ~ m1_pre_topc(X10,X11) ) ),
    inference(subsumption_resolution,[],[f178,f36])).

fof(f178,plain,(
    ! [X10,X11] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(X10)
      | ~ m1_pre_topc(X10,sK0)
      | v2_struct_0(X11)
      | ~ m1_pre_topc(X11,sK0)
      | k1_tsep_1(sK0,X10,X11) = g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11))
      | ~ m1_pre_topc(X10,X11) ) ),
    inference(subsumption_resolution,[],[f170,f34])).

fof(f170,plain,(
    ! [X10,X11] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X10)
      | ~ m1_pre_topc(X10,sK0)
      | v2_struct_0(X11)
      | ~ m1_pre_topc(X11,sK0)
      | k1_tsep_1(sK0,X10,X11) = g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11))
      | ~ m1_pre_topc(X10,X11) ) ),
    inference(resolution,[],[f35,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ m1_pre_topc(X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f1095,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f1094,f618])).

fof(f618,plain,(
    ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f613,f32])).

fof(f613,plain,
    ( v2_struct_0(sK1)
    | ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(resolution,[],[f324,f33])).

fof(f324,plain,(
    ! [X11] :
      ( ~ m1_pre_topc(X11,sK0)
      | v2_struct_0(X11)
      | ~ v2_struct_0(k1_tsep_1(sK0,X11,sK2)) ) ),
    inference(subsumption_resolution,[],[f323,f30])).

fof(f323,plain,(
    ! [X11] :
      ( v2_struct_0(X11)
      | ~ m1_pre_topc(X11,sK0)
      | v2_struct_0(sK2)
      | ~ v2_struct_0(k1_tsep_1(sK0,X11,sK2)) ) ),
    inference(subsumption_resolution,[],[f322,f36])).

fof(f322,plain,(
    ! [X11] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(X11)
      | ~ m1_pre_topc(X11,sK0)
      | v2_struct_0(sK2)
      | ~ v2_struct_0(k1_tsep_1(sK0,X11,sK2)) ) ),
    inference(subsumption_resolution,[],[f312,f34])).

fof(f312,plain,(
    ! [X11] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X11)
      | ~ m1_pre_topc(X11,sK0)
      | v2_struct_0(sK2)
      | ~ v2_struct_0(k1_tsep_1(sK0,X11,sK2)) ) ),
    inference(resolution,[],[f31,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1094,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f1093,f31])).

fof(f1093,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f1092,f30])).

fof(f1092,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f1091,f36])).

fof(f1091,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f1090,f34])).

fof(f1090,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f1079,f1085])).

fof(f1085,plain,(
    v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f1084,f31])).

fof(f1084,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK2,sK0) ),
    inference(subsumption_resolution,[],[f1083,f30])).

fof(f1083,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0) ),
    inference(subsumption_resolution,[],[f1082,f36])).

fof(f1082,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0) ),
    inference(subsumption_resolution,[],[f1081,f34])).

fof(f1081,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0) ),
    inference(duplicate_literal_removal,[],[f1073])).

fof(f1073,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0) ),
    inference(superposition,[],[f47,f1064])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v1_pre_topc(k1_tsep_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1079,plain,
    ( ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f1076])).

fof(f1076,plain,
    ( ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(superposition,[],[f49,f1064])).

fof(f49,plain,(
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
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f5687,plain,(
    r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f5686,f26])).

fof(f26,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f5686,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ m1_pre_topc(sK3,sK0) ),
    inference(subsumption_resolution,[],[f5685,f25])).

fof(f25,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f5685,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0) ),
    inference(subsumption_resolution,[],[f5684,f33])).

fof(f5684,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0) ),
    inference(subsumption_resolution,[],[f5683,f32])).

fof(f5683,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0) ),
    inference(subsumption_resolution,[],[f5643,f1089])).

fof(f5643,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0) ),
    inference(resolution,[],[f5639,f737])).

fof(f737,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_pre_topc(k1_tsep_1(sK0,X7,X8),X6)
      | ~ m1_pre_topc(X6,sK0)
      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,X7,X8)),u1_struct_0(X6))
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X7,sK0)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(X8,sK0) ) ),
    inference(subsumption_resolution,[],[f736,f36])).

fof(f736,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_pre_topc(X6,sK0)
      | ~ m1_pre_topc(k1_tsep_1(sK0,X7,X8),X6)
      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,X7,X8)),u1_struct_0(X6))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X7,sK0)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(X8,sK0) ) ),
    inference(subsumption_resolution,[],[f732,f34])).

fof(f732,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_pre_topc(X6,sK0)
      | ~ m1_pre_topc(k1_tsep_1(sK0,X7,X8),X6)
      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,X7,X8)),u1_struct_0(X6))
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X7,sK0)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(X8,sK0) ) ),
    inference(resolution,[],[f172,f48])).

fof(f5639,plain,(
    m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f5638,f28])).

fof(f28,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f5638,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f5629,f30])).

fof(f5629,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2)) ),
    inference(resolution,[],[f4524,f31])).

fof(f4524,plain,(
    ! [X13] :
      ( ~ m1_pre_topc(X13,sK0)
      | v2_struct_0(X13)
      | ~ m1_pre_topc(sK3,X13)
      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,X13)) ) ),
    inference(subsumption_resolution,[],[f4517,f25])).

fof(f4517,plain,(
    ! [X13] :
      ( v2_struct_0(sK3)
      | v2_struct_0(X13)
      | ~ m1_pre_topc(X13,sK0)
      | ~ m1_pre_topc(sK3,X13)
      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,X13)) ) ),
    inference(resolution,[],[f3580,f26])).

fof(f3580,plain,(
    ! [X14,X15] :
      ( ~ m1_pre_topc(X14,sK0)
      | v2_struct_0(X14)
      | v2_struct_0(X15)
      | ~ m1_pre_topc(X15,sK0)
      | ~ m1_pre_topc(X14,X15)
      | m1_pre_topc(k1_tsep_1(sK0,sK1,X14),k1_tsep_1(sK0,sK1,X15)) ) ),
    inference(subsumption_resolution,[],[f3579,f880])).

fof(f880,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(subsumption_resolution,[],[f879,f797])).

fof(f797,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f792,f32])).

fof(f792,plain,
    ( v2_struct_0(sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK0,sK1,sK1) ),
    inference(resolution,[],[f181,f33])).

fof(f879,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k1_tsep_1(sK0,sK1,sK1)
    | m1_pre_topc(sK1,sK1) ),
    inference(subsumption_resolution,[],[f874,f32])).

fof(f874,plain,
    ( v2_struct_0(sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k1_tsep_1(sK0,sK1,sK1)
    | m1_pre_topc(sK1,sK1) ),
    inference(resolution,[],[f835,f33])).

fof(f835,plain,(
    ! [X9] :
      ( ~ m1_pre_topc(X9,sK0)
      | v2_struct_0(X9)
      | g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)) != k1_tsep_1(sK0,sK1,X9)
      | m1_pre_topc(sK1,X9) ) ),
    inference(subsumption_resolution,[],[f830,f32])).

fof(f830,plain,(
    ! [X9] :
      ( v2_struct_0(sK1)
      | v2_struct_0(X9)
      | ~ m1_pre_topc(X9,sK0)
      | g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)) != k1_tsep_1(sK0,sK1,X9)
      | m1_pre_topc(sK1,X9) ) ),
    inference(resolution,[],[f177,f33])).

fof(f3579,plain,(
    ! [X14,X15] :
      ( v2_struct_0(X14)
      | ~ m1_pre_topc(X14,sK0)
      | v2_struct_0(X15)
      | ~ m1_pre_topc(X15,sK0)
      | ~ m1_pre_topc(sK1,sK1)
      | ~ m1_pre_topc(X14,X15)
      | m1_pre_topc(k1_tsep_1(sK0,sK1,X14),k1_tsep_1(sK0,sK1,X15)) ) ),
    inference(subsumption_resolution,[],[f3572,f32])).

fof(f3572,plain,(
    ! [X14,X15] :
      ( v2_struct_0(sK1)
      | v2_struct_0(X14)
      | ~ m1_pre_topc(X14,sK0)
      | v2_struct_0(X15)
      | ~ m1_pre_topc(X15,sK0)
      | ~ m1_pre_topc(sK1,sK1)
      | ~ m1_pre_topc(X14,X15)
      | m1_pre_topc(k1_tsep_1(sK0,sK1,X14),k1_tsep_1(sK0,sK1,X15)) ) ),
    inference(resolution,[],[f936,f33])).

fof(f936,plain,(
    ! [X17,X15,X16] :
      ( ~ m1_pre_topc(X15,sK0)
      | v2_struct_0(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,sK0)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,sK0)
      | ~ m1_pre_topc(sK1,X15)
      | ~ m1_pre_topc(X16,X17)
      | m1_pre_topc(k1_tsep_1(sK0,sK1,X16),k1_tsep_1(sK0,X15,X17)) ) ),
    inference(subsumption_resolution,[],[f931,f32])).

fof(f931,plain,(
    ! [X17,X15,X16] :
      ( v2_struct_0(sK1)
      | v2_struct_0(X15)
      | ~ m1_pre_topc(X15,sK0)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,sK0)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,sK0)
      | ~ m1_pre_topc(sK1,X15)
      | ~ m1_pre_topc(X16,X17)
      | m1_pre_topc(k1_tsep_1(sK0,sK1,X16),k1_tsep_1(sK0,X15,X17)) ) ),
    inference(resolution,[],[f175,f33])).

fof(f175,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_pre_topc(X4,sK0)
      | v2_struct_0(X4)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,sK0)
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X6,sK0)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X7,sK0)
      | ~ m1_pre_topc(X4,X5)
      | ~ m1_pre_topc(X6,X7)
      | m1_pre_topc(k1_tsep_1(sK0,X4,X6),k1_tsep_1(sK0,X5,X7)) ) ),
    inference(subsumption_resolution,[],[f174,f36])).

fof(f174,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,sK0)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,sK0)
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X6,sK0)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X7,sK0)
      | ~ m1_pre_topc(X4,X5)
      | ~ m1_pre_topc(X6,X7)
      | m1_pre_topc(k1_tsep_1(sK0,X4,X6),k1_tsep_1(sK0,X5,X7)) ) ),
    inference(subsumption_resolution,[],[f168,f34])).

fof(f168,plain,(
    ! [X6,X4,X7,X5] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,sK0)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,sK0)
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X6,sK0)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X7,sK0)
      | ~ m1_pre_topc(X4,X5)
      | ~ m1_pre_topc(X6,X7)
      | m1_pre_topc(k1_tsep_1(sK0,X4,X6),k1_tsep_1(sK0,X5,X7)) ) ),
    inference(resolution,[],[f35,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
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
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X4)
      | m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))
                      | ~ m1_pre_topc(X3,X4)
                      | ~ m1_pre_topc(X1,X2)
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))
                      | ~ m1_pre_topc(X3,X4)
                      | ~ m1_pre_topc(X1,X2)
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
                     => ( ( m1_pre_topc(X3,X4)
                          & m1_pre_topc(X1,X2) )
                       => m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tmap_1)).

fof(f8579,plain,(
    ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f8578,f25])).

fof(f8578,plain,
    ( v2_struct_0(sK3)
    | ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f8572,f29])).

fof(f29,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f8572,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | v2_struct_0(sK3)
    | ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2)) ),
    inference(resolution,[],[f6419,f26])).

fof(f6419,plain,(
    ! [X11] :
      ( ~ m1_pre_topc(X11,sK0)
      | m1_pre_topc(k1_tsep_1(sK0,sK1,X11),sK2)
      | v2_struct_0(X11)
      | ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,X11)),u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f6412,f32])).

fof(f6412,plain,(
    ! [X11] :
      ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,X11)),u1_struct_0(sK2))
      | v2_struct_0(sK1)
      | m1_pre_topc(k1_tsep_1(sK0,sK1,X11),sK2)
      | v2_struct_0(X11)
      | ~ m1_pre_topc(X11,sK0) ) ),
    inference(resolution,[],[f3548,f33])).

fof(f3548,plain,(
    ! [X17,X16] :
      ( ~ m1_pre_topc(X16,sK0)
      | ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,X16,X17)),u1_struct_0(sK2))
      | v2_struct_0(X16)
      | m1_pre_topc(k1_tsep_1(sK0,X16,X17),sK2)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,sK0) ) ),
    inference(resolution,[],[f761,f31])).

fof(f761,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_pre_topc(X6,sK0)
      | m1_pre_topc(k1_tsep_1(sK0,X7,X8),X6)
      | ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,X7,X8)),u1_struct_0(X6))
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X7,sK0)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(X8,sK0) ) ),
    inference(subsumption_resolution,[],[f760,f36])).

fof(f760,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_pre_topc(X6,sK0)
      | m1_pre_topc(k1_tsep_1(sK0,X7,X8),X6)
      | ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,X7,X8)),u1_struct_0(X6))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X7,sK0)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(X8,sK0) ) ),
    inference(subsumption_resolution,[],[f756,f34])).

fof(f756,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_pre_topc(X6,sK0)
      | m1_pre_topc(k1_tsep_1(sK0,X7,X8),X6)
      | ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,X7,X8)),u1_struct_0(X6))
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X7,sK0)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(X8,sK0) ) ),
    inference(resolution,[],[f173,f48])).

fof(f173,plain,(
    ! [X2,X3] :
      ( ~ m1_pre_topc(X2,sK0)
      | ~ m1_pre_topc(X3,sK0)
      | m1_pre_topc(X2,X3)
      | ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f167,f36])).

fof(f167,plain,(
    ! [X2,X3] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X2,sK0)
      | ~ m1_pre_topc(X3,sK0)
      | m1_pre_topc(X2,X3)
      | ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X3)) ) ),
    inference(resolution,[],[f35,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:52:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.40  % (18969)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.46  % (18956)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (18963)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (18956)Refutation not found, incomplete strategy% (18956)------------------------------
% 0.20/0.48  % (18956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (18956)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (18956)Memory used [KB]: 6268
% 0.20/0.48  % (18956)Time elapsed: 0.066 s
% 0.20/0.48  % (18956)------------------------------
% 0.20/0.48  % (18956)------------------------------
% 0.20/0.48  % (18960)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (18971)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.49  % (18961)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (18973)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.49  % (18959)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (18958)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (18962)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (18957)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (18957)Refutation not found, incomplete strategy% (18957)------------------------------
% 0.20/0.50  % (18957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (18957)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (18957)Memory used [KB]: 10618
% 0.20/0.50  % (18957)Time elapsed: 0.092 s
% 0.20/0.50  % (18957)------------------------------
% 0.20/0.50  % (18957)------------------------------
% 0.20/0.50  % (18976)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (18976)Refutation not found, incomplete strategy% (18976)------------------------------
% 0.20/0.50  % (18976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (18976)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (18976)Memory used [KB]: 10618
% 0.20/0.50  % (18976)Time elapsed: 0.096 s
% 0.20/0.50  % (18976)------------------------------
% 0.20/0.50  % (18976)------------------------------
% 0.20/0.50  % (18970)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.50  % (18975)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  % (18974)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.50  % (18964)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.51  % (18968)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (18965)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.51  % (18967)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.51  % (18966)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.51  % (18972)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.52  % (18969)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f8580,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f8579,f5688])).
% 0.20/0.52  fof(f5688,plain,(
% 0.20/0.52    r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))),
% 0.20/0.52    inference(forward_demodulation,[],[f5687,f1097])).
% 0.20/0.52  fof(f1097,plain,(
% 0.20/0.52    u1_struct_0(sK2) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 0.20/0.52    inference(forward_demodulation,[],[f1096,f1002])).
% 0.20/0.52  fof(f1002,plain,(
% 0.20/0.52    u1_struct_0(sK2) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2))),
% 0.20/0.52    inference(resolution,[],[f959,f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.52  fof(f959,plain,(
% 0.20/0.52    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2))),
% 0.20/0.52    inference(resolution,[],[f956,f766])).
% 0.20/0.52  fof(f766,plain,(
% 0.20/0.52    ~m1_pre_topc(sK2,sK2) | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2))),
% 0.20/0.52    inference(resolution,[],[f734,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    m1_pre_topc(sK2,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f10])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & (m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,negated_conjecture,(
% 0.20/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 0.20/0.52    inference(negated_conjecture,[],[f8])).
% 0.20/0.52  fof(f8,conjecture,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tmap_1)).
% 0.20/0.52  fof(f734,plain,(
% 0.20/0.52    ( ! [X10] : (~m1_pre_topc(X10,sK0) | ~m1_pre_topc(sK2,X10) | r1_tarski(u1_struct_0(sK2),u1_struct_0(X10))) )),
% 0.20/0.52    inference(resolution,[],[f172,f31])).
% 0.20/0.52  fof(f172,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,X1) | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f166,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    l1_pre_topc(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f166,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,X1) | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))) )),
% 0.20/0.52    inference(resolution,[],[f35,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    v2_pre_topc(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f956,plain,(
% 0.20/0.52    m1_pre_topc(sK2,sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f955,f798])).
% 0.20/0.52  fof(f798,plain,(
% 0.20/0.52    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f793,f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ~v2_struct_0(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f793,plain,(
% 0.20/0.52    v2_struct_0(sK2) | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)),
% 0.20/0.52    inference(resolution,[],[f181,f31])).
% 0.20/0.52  fof(f181,plain,(
% 0.20/0.52    ( ! [X12] : (~m1_pre_topc(X12,sK0) | v2_struct_0(X12) | k1_tsep_1(sK0,X12,X12) = g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f180,f36])).
% 0.20/0.52  fof(f180,plain,(
% 0.20/0.52    ( ! [X12] : (~l1_pre_topc(sK0) | v2_struct_0(X12) | ~m1_pre_topc(X12,sK0) | k1_tsep_1(sK0,X12,X12) = g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f171,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ~v2_struct_0(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f171,plain,(
% 0.20/0.52    ( ! [X12] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X12) | ~m1_pre_topc(X12,sK0) | k1_tsep_1(sK0,X12,X12) = g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12))) )),
% 0.20/0.52    inference(resolution,[],[f35,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tmap_1)).
% 0.20/0.52  fof(f955,plain,(
% 0.20/0.52    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k1_tsep_1(sK0,sK2,sK2) | m1_pre_topc(sK2,sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f949,f30])).
% 0.20/0.52  fof(f949,plain,(
% 0.20/0.52    v2_struct_0(sK2) | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k1_tsep_1(sK0,sK2,sK2) | m1_pre_topc(sK2,sK2)),
% 0.20/0.52    inference(resolution,[],[f836,f31])).
% 0.20/0.52  fof(f836,plain,(
% 0.20/0.52    ( ! [X10] : (~m1_pre_topc(X10,sK0) | v2_struct_0(X10) | k1_tsep_1(sK0,sK2,X10) != g1_pre_topc(u1_struct_0(X10),u1_pre_topc(X10)) | m1_pre_topc(sK2,X10)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f831,f30])).
% 0.20/0.52  fof(f831,plain,(
% 0.20/0.52    ( ! [X10] : (v2_struct_0(sK2) | v2_struct_0(X10) | ~m1_pre_topc(X10,sK0) | k1_tsep_1(sK0,sK2,X10) != g1_pre_topc(u1_struct_0(X10),u1_pre_topc(X10)) | m1_pre_topc(sK2,X10)) )),
% 0.20/0.52    inference(resolution,[],[f177,f31])).
% 0.20/0.52  fof(f177,plain,(
% 0.20/0.52    ( ! [X8,X9] : (~m1_pre_topc(X8,sK0) | v2_struct_0(X8) | v2_struct_0(X9) | ~m1_pre_topc(X9,sK0) | k1_tsep_1(sK0,X8,X9) != g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)) | m1_pre_topc(X8,X9)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f176,f36])).
% 0.20/0.52  fof(f176,plain,(
% 0.20/0.52    ( ! [X8,X9] : (~l1_pre_topc(sK0) | v2_struct_0(X8) | ~m1_pre_topc(X8,sK0) | v2_struct_0(X9) | ~m1_pre_topc(X9,sK0) | k1_tsep_1(sK0,X8,X9) != g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)) | m1_pre_topc(X8,X9)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f169,f34])).
% 0.20/0.52  fof(f169,plain,(
% 0.20/0.52    ( ! [X8,X9] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X8) | ~m1_pre_topc(X8,sK0) | v2_struct_0(X9) | ~m1_pre_topc(X9,sK0) | k1_tsep_1(sK0,X8,X9) != g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)) | m1_pre_topc(X8,X9)) )),
% 0.20/0.52    inference(resolution,[],[f35,f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | m1_pre_topc(X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tsep_1)).
% 0.20/0.52  fof(f1096,plain,(
% 0.20/0.52    k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f1095,f1089])).
% 0.20/0.52  fof(f1089,plain,(
% 0.20/0.52    m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f1088,f31])).
% 0.20/0.52  fof(f1088,plain,(
% 0.20/0.52    m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | ~m1_pre_topc(sK2,sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f1087,f30])).
% 0.20/0.52  fof(f1087,plain,(
% 0.20/0.52    m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f1086,f36])).
% 0.20/0.52  fof(f1086,plain,(
% 0.20/0.52    m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f1080,f34])).
% 0.20/0.52  fof(f1080,plain,(
% 0.20/0.52    m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f1074])).
% 0.20/0.52  fof(f1074,plain,(
% 0.20/0.52    m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0)),
% 0.20/0.52    inference(superposition,[],[f48,f1064])).
% 0.20/0.52  fof(f1064,plain,(
% 0.20/0.52    k1_tsep_1(sK0,sK2,sK2) = k1_tsep_1(sK0,sK1,sK2)),
% 0.20/0.52    inference(backward_demodulation,[],[f798,f1063])).
% 0.20/0.52  fof(f1063,plain,(
% 0.20/0.52    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK1,sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f1062,f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    m1_pre_topc(sK1,sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f1062,plain,(
% 0.20/0.52    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK1,sK2) | ~m1_pre_topc(sK1,sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f1058,f30])).
% 0.20/0.52  fof(f1058,plain,(
% 0.20/0.52    v2_struct_0(sK2) | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK1,sK2) | ~m1_pre_topc(sK1,sK2)),
% 0.20/0.52    inference(resolution,[],[f867,f31])).
% 0.20/0.52  fof(f867,plain,(
% 0.20/0.52    ( ! [X9] : (~m1_pre_topc(X9,sK0) | v2_struct_0(X9) | g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)) = k1_tsep_1(sK0,sK1,X9) | ~m1_pre_topc(sK1,X9)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f862,f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ~v2_struct_0(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f862,plain,(
% 0.20/0.52    ( ! [X9] : (v2_struct_0(sK1) | v2_struct_0(X9) | ~m1_pre_topc(X9,sK0) | g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)) = k1_tsep_1(sK0,sK1,X9) | ~m1_pre_topc(sK1,X9)) )),
% 0.20/0.52    inference(resolution,[],[f179,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    m1_pre_topc(sK1,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f179,plain,(
% 0.20/0.52    ( ! [X10,X11] : (~m1_pre_topc(X10,sK0) | v2_struct_0(X10) | v2_struct_0(X11) | ~m1_pre_topc(X11,sK0) | k1_tsep_1(sK0,X10,X11) = g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)) | ~m1_pre_topc(X10,X11)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f178,f36])).
% 0.20/0.52  fof(f178,plain,(
% 0.20/0.52    ( ! [X10,X11] : (~l1_pre_topc(sK0) | v2_struct_0(X10) | ~m1_pre_topc(X10,sK0) | v2_struct_0(X11) | ~m1_pre_topc(X11,sK0) | k1_tsep_1(sK0,X10,X11) = g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)) | ~m1_pre_topc(X10,X11)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f170,f34])).
% 0.20/0.52  fof(f170,plain,(
% 0.20/0.52    ( ! [X10,X11] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X10) | ~m1_pre_topc(X10,sK0) | v2_struct_0(X11) | ~m1_pre_topc(X11,sK0) | k1_tsep_1(sK0,X10,X11) = g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)) | ~m1_pre_topc(X10,X11)) )),
% 0.20/0.52    inference(resolution,[],[f35,f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 0.20/0.52  fof(f1095,plain,(
% 0.20/0.52    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f1094,f618])).
% 0.20/0.52  fof(f618,plain,(
% 0.20/0.52    ~v2_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f613,f32])).
% 0.20/0.52  fof(f613,plain,(
% 0.20/0.52    v2_struct_0(sK1) | ~v2_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 0.20/0.52    inference(resolution,[],[f324,f33])).
% 0.20/0.52  fof(f324,plain,(
% 0.20/0.52    ( ! [X11] : (~m1_pre_topc(X11,sK0) | v2_struct_0(X11) | ~v2_struct_0(k1_tsep_1(sK0,X11,sK2))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f323,f30])).
% 0.20/0.52  fof(f323,plain,(
% 0.20/0.52    ( ! [X11] : (v2_struct_0(X11) | ~m1_pre_topc(X11,sK0) | v2_struct_0(sK2) | ~v2_struct_0(k1_tsep_1(sK0,X11,sK2))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f322,f36])).
% 0.20/0.52  fof(f322,plain,(
% 0.20/0.52    ( ! [X11] : (~l1_pre_topc(sK0) | v2_struct_0(X11) | ~m1_pre_topc(X11,sK0) | v2_struct_0(sK2) | ~v2_struct_0(k1_tsep_1(sK0,X11,sK2))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f312,f34])).
% 0.20/0.52  fof(f312,plain,(
% 0.20/0.52    ( ! [X11] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X11) | ~m1_pre_topc(X11,sK0) | v2_struct_0(sK2) | ~v2_struct_0(k1_tsep_1(sK0,X11,sK2))) )),
% 0.20/0.52    inference(resolution,[],[f31,f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~v2_struct_0(k1_tsep_1(X0,X1,X2))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f1094,plain,(
% 0.20/0.52    v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f1093,f31])).
% 0.20/0.52  fof(f1093,plain,(
% 0.20/0.52    ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f1092,f30])).
% 0.20/0.52  fof(f1092,plain,(
% 0.20/0.52    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f1091,f36])).
% 0.20/0.52  fof(f1091,plain,(
% 0.20/0.52    ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f1090,f34])).
% 0.20/0.52  fof(f1090,plain,(
% 0.20/0.52    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f1079,f1085])).
% 0.20/0.52  fof(f1085,plain,(
% 0.20/0.52    v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f1084,f31])).
% 0.20/0.52  fof(f1084,plain,(
% 0.20/0.52    v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(sK2,sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f1083,f30])).
% 0.20/0.52  fof(f1083,plain,(
% 0.20/0.52    v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f1082,f36])).
% 0.20/0.52  fof(f1082,plain,(
% 0.20/0.52    v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f1081,f34])).
% 0.20/0.52  fof(f1081,plain,(
% 0.20/0.52    v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f1073])).
% 0.20/0.52  fof(f1073,plain,(
% 0.20/0.52    v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0)),
% 0.20/0.52    inference(superposition,[],[f47,f1064])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v1_pre_topc(k1_tsep_1(X0,X1,X2))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f1079,plain,(
% 0.20/0.52    ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f1076])).
% 0.20/0.52  fof(f1076,plain,(
% 0.20/0.52    ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 0.20/0.52    inference(superposition,[],[f49,f1064])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))) )),
% 0.20/0.52    inference(equality_resolution,[],[f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~v1_pre_topc(X3) | ~m1_pre_topc(X3,X0) | u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).
% 0.20/0.52  fof(f5687,plain,(
% 0.20/0.52    r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 0.20/0.52    inference(subsumption_resolution,[],[f5686,f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    m1_pre_topc(sK3,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f5686,plain,(
% 0.20/0.52    r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | ~m1_pre_topc(sK3,sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f5685,f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ~v2_struct_0(sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f5685,plain,(
% 0.20/0.52    r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f5684,f33])).
% 0.20/0.52  fof(f5684,plain,(
% 0.20/0.52    r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f5683,f32])).
% 0.20/0.52  fof(f5683,plain,(
% 0.20/0.52    r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f5643,f1089])).
% 0.20/0.52  fof(f5643,plain,(
% 0.20/0.52    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0)),
% 0.20/0.52    inference(resolution,[],[f5639,f737])).
% 0.20/0.52  fof(f737,plain,(
% 0.20/0.52    ( ! [X6,X8,X7] : (~m1_pre_topc(k1_tsep_1(sK0,X7,X8),X6) | ~m1_pre_topc(X6,sK0) | r1_tarski(u1_struct_0(k1_tsep_1(sK0,X7,X8)),u1_struct_0(X6)) | v2_struct_0(X7) | ~m1_pre_topc(X7,sK0) | v2_struct_0(X8) | ~m1_pre_topc(X8,sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f736,f36])).
% 0.20/0.52  fof(f736,plain,(
% 0.20/0.52    ( ! [X6,X8,X7] : (~m1_pre_topc(X6,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,X7,X8),X6) | r1_tarski(u1_struct_0(k1_tsep_1(sK0,X7,X8)),u1_struct_0(X6)) | ~l1_pre_topc(sK0) | v2_struct_0(X7) | ~m1_pre_topc(X7,sK0) | v2_struct_0(X8) | ~m1_pre_topc(X8,sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f732,f34])).
% 0.20/0.52  fof(f732,plain,(
% 0.20/0.52    ( ! [X6,X8,X7] : (~m1_pre_topc(X6,sK0) | ~m1_pre_topc(k1_tsep_1(sK0,X7,X8),X6) | r1_tarski(u1_struct_0(k1_tsep_1(sK0,X7,X8)),u1_struct_0(X6)) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X7) | ~m1_pre_topc(X7,sK0) | v2_struct_0(X8) | ~m1_pre_topc(X8,sK0)) )),
% 0.20/0.52    inference(resolution,[],[f172,f48])).
% 0.20/0.52  fof(f5639,plain,(
% 0.20/0.52    m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f5638,f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    m1_pre_topc(sK3,sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f5638,plain,(
% 0.20/0.52    ~m1_pre_topc(sK3,sK2) | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f5629,f30])).
% 0.20/0.52  fof(f5629,plain,(
% 0.20/0.52    v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK2) | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2))),
% 0.20/0.52    inference(resolution,[],[f4524,f31])).
% 0.20/0.52  fof(f4524,plain,(
% 0.20/0.52    ( ! [X13] : (~m1_pre_topc(X13,sK0) | v2_struct_0(X13) | ~m1_pre_topc(sK3,X13) | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,X13))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f4517,f25])).
% 0.20/0.52  fof(f4517,plain,(
% 0.20/0.52    ( ! [X13] : (v2_struct_0(sK3) | v2_struct_0(X13) | ~m1_pre_topc(X13,sK0) | ~m1_pre_topc(sK3,X13) | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,X13))) )),
% 0.20/0.52    inference(resolution,[],[f3580,f26])).
% 0.20/0.52  fof(f3580,plain,(
% 0.20/0.52    ( ! [X14,X15] : (~m1_pre_topc(X14,sK0) | v2_struct_0(X14) | v2_struct_0(X15) | ~m1_pre_topc(X15,sK0) | ~m1_pre_topc(X14,X15) | m1_pre_topc(k1_tsep_1(sK0,sK1,X14),k1_tsep_1(sK0,sK1,X15))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f3579,f880])).
% 0.20/0.52  fof(f880,plain,(
% 0.20/0.52    m1_pre_topc(sK1,sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f879,f797])).
% 0.20/0.52  fof(f797,plain,(
% 0.20/0.52    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK0,sK1,sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f792,f32])).
% 0.20/0.52  fof(f792,plain,(
% 0.20/0.52    v2_struct_0(sK1) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK0,sK1,sK1)),
% 0.20/0.52    inference(resolution,[],[f181,f33])).
% 0.20/0.52  fof(f879,plain,(
% 0.20/0.52    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k1_tsep_1(sK0,sK1,sK1) | m1_pre_topc(sK1,sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f874,f32])).
% 0.20/0.52  fof(f874,plain,(
% 0.20/0.52    v2_struct_0(sK1) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k1_tsep_1(sK0,sK1,sK1) | m1_pre_topc(sK1,sK1)),
% 0.20/0.52    inference(resolution,[],[f835,f33])).
% 0.20/0.52  fof(f835,plain,(
% 0.20/0.52    ( ! [X9] : (~m1_pre_topc(X9,sK0) | v2_struct_0(X9) | g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)) != k1_tsep_1(sK0,sK1,X9) | m1_pre_topc(sK1,X9)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f830,f32])).
% 0.20/0.52  fof(f830,plain,(
% 0.20/0.52    ( ! [X9] : (v2_struct_0(sK1) | v2_struct_0(X9) | ~m1_pre_topc(X9,sK0) | g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)) != k1_tsep_1(sK0,sK1,X9) | m1_pre_topc(sK1,X9)) )),
% 0.20/0.52    inference(resolution,[],[f177,f33])).
% 0.20/0.52  fof(f3579,plain,(
% 0.20/0.52    ( ! [X14,X15] : (v2_struct_0(X14) | ~m1_pre_topc(X14,sK0) | v2_struct_0(X15) | ~m1_pre_topc(X15,sK0) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(X14,X15) | m1_pre_topc(k1_tsep_1(sK0,sK1,X14),k1_tsep_1(sK0,sK1,X15))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f3572,f32])).
% 0.20/0.52  fof(f3572,plain,(
% 0.20/0.52    ( ! [X14,X15] : (v2_struct_0(sK1) | v2_struct_0(X14) | ~m1_pre_topc(X14,sK0) | v2_struct_0(X15) | ~m1_pre_topc(X15,sK0) | ~m1_pre_topc(sK1,sK1) | ~m1_pre_topc(X14,X15) | m1_pre_topc(k1_tsep_1(sK0,sK1,X14),k1_tsep_1(sK0,sK1,X15))) )),
% 0.20/0.52    inference(resolution,[],[f936,f33])).
% 0.20/0.52  fof(f936,plain,(
% 0.20/0.52    ( ! [X17,X15,X16] : (~m1_pre_topc(X15,sK0) | v2_struct_0(X15) | v2_struct_0(X16) | ~m1_pre_topc(X16,sK0) | v2_struct_0(X17) | ~m1_pre_topc(X17,sK0) | ~m1_pre_topc(sK1,X15) | ~m1_pre_topc(X16,X17) | m1_pre_topc(k1_tsep_1(sK0,sK1,X16),k1_tsep_1(sK0,X15,X17))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f931,f32])).
% 0.20/0.52  fof(f931,plain,(
% 0.20/0.52    ( ! [X17,X15,X16] : (v2_struct_0(sK1) | v2_struct_0(X15) | ~m1_pre_topc(X15,sK0) | v2_struct_0(X16) | ~m1_pre_topc(X16,sK0) | v2_struct_0(X17) | ~m1_pre_topc(X17,sK0) | ~m1_pre_topc(sK1,X15) | ~m1_pre_topc(X16,X17) | m1_pre_topc(k1_tsep_1(sK0,sK1,X16),k1_tsep_1(sK0,X15,X17))) )),
% 0.20/0.52    inference(resolution,[],[f175,f33])).
% 0.20/0.52  fof(f175,plain,(
% 0.20/0.52    ( ! [X6,X4,X7,X5] : (~m1_pre_topc(X4,sK0) | v2_struct_0(X4) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK0) | v2_struct_0(X6) | ~m1_pre_topc(X6,sK0) | v2_struct_0(X7) | ~m1_pre_topc(X7,sK0) | ~m1_pre_topc(X4,X5) | ~m1_pre_topc(X6,X7) | m1_pre_topc(k1_tsep_1(sK0,X4,X6),k1_tsep_1(sK0,X5,X7))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f174,f36])).
% 0.20/0.52  fof(f174,plain,(
% 0.20/0.52    ( ! [X6,X4,X7,X5] : (~l1_pre_topc(sK0) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK0) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK0) | v2_struct_0(X6) | ~m1_pre_topc(X6,sK0) | v2_struct_0(X7) | ~m1_pre_topc(X7,sK0) | ~m1_pre_topc(X4,X5) | ~m1_pre_topc(X6,X7) | m1_pre_topc(k1_tsep_1(sK0,X4,X6),k1_tsep_1(sK0,X5,X7))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f168,f34])).
% 0.20/0.52  fof(f168,plain,(
% 0.20/0.52    ( ! [X6,X4,X7,X5] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK0) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK0) | v2_struct_0(X6) | ~m1_pre_topc(X6,sK0) | v2_struct_0(X7) | ~m1_pre_topc(X7,sK0) | ~m1_pre_topc(X4,X5) | ~m1_pre_topc(X6,X7) | m1_pre_topc(k1_tsep_1(sK0,X4,X6),k1_tsep_1(sK0,X5,X7))) )),
% 0.20/0.52    inference(resolution,[],[f35,f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X4) | ~m1_pre_topc(X4,X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X4) | m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4)) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4)) | (~m1_pre_topc(X3,X4) | ~m1_pre_topc(X1,X2))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tmap_1)).
% 0.20/0.52  fof(f8579,plain,(
% 0.20/0.52    ~r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f8578,f25])).
% 0.20/0.52  fof(f8578,plain,(
% 0.20/0.52    v2_struct_0(sK3) | ~r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f8572,f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f8572,plain,(
% 0.20/0.52    m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) | v2_struct_0(sK3) | ~r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))),
% 0.20/0.52    inference(resolution,[],[f6419,f26])).
% 0.20/0.52  fof(f6419,plain,(
% 0.20/0.52    ( ! [X11] : (~m1_pre_topc(X11,sK0) | m1_pre_topc(k1_tsep_1(sK0,sK1,X11),sK2) | v2_struct_0(X11) | ~r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,X11)),u1_struct_0(sK2))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f6412,f32])).
% 0.20/0.52  fof(f6412,plain,(
% 0.20/0.52    ( ! [X11] : (~r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,X11)),u1_struct_0(sK2)) | v2_struct_0(sK1) | m1_pre_topc(k1_tsep_1(sK0,sK1,X11),sK2) | v2_struct_0(X11) | ~m1_pre_topc(X11,sK0)) )),
% 0.20/0.52    inference(resolution,[],[f3548,f33])).
% 0.20/0.52  fof(f3548,plain,(
% 0.20/0.52    ( ! [X17,X16] : (~m1_pre_topc(X16,sK0) | ~r1_tarski(u1_struct_0(k1_tsep_1(sK0,X16,X17)),u1_struct_0(sK2)) | v2_struct_0(X16) | m1_pre_topc(k1_tsep_1(sK0,X16,X17),sK2) | v2_struct_0(X17) | ~m1_pre_topc(X17,sK0)) )),
% 0.20/0.52    inference(resolution,[],[f761,f31])).
% 0.20/0.52  fof(f761,plain,(
% 0.20/0.52    ( ! [X6,X8,X7] : (~m1_pre_topc(X6,sK0) | m1_pre_topc(k1_tsep_1(sK0,X7,X8),X6) | ~r1_tarski(u1_struct_0(k1_tsep_1(sK0,X7,X8)),u1_struct_0(X6)) | v2_struct_0(X7) | ~m1_pre_topc(X7,sK0) | v2_struct_0(X8) | ~m1_pre_topc(X8,sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f760,f36])).
% 0.20/0.52  fof(f760,plain,(
% 0.20/0.52    ( ! [X6,X8,X7] : (~m1_pre_topc(X6,sK0) | m1_pre_topc(k1_tsep_1(sK0,X7,X8),X6) | ~r1_tarski(u1_struct_0(k1_tsep_1(sK0,X7,X8)),u1_struct_0(X6)) | ~l1_pre_topc(sK0) | v2_struct_0(X7) | ~m1_pre_topc(X7,sK0) | v2_struct_0(X8) | ~m1_pre_topc(X8,sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f756,f34])).
% 0.20/0.52  fof(f756,plain,(
% 0.20/0.52    ( ! [X6,X8,X7] : (~m1_pre_topc(X6,sK0) | m1_pre_topc(k1_tsep_1(sK0,X7,X8),X6) | ~r1_tarski(u1_struct_0(k1_tsep_1(sK0,X7,X8)),u1_struct_0(X6)) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X7) | ~m1_pre_topc(X7,sK0) | v2_struct_0(X8) | ~m1_pre_topc(X8,sK0)) )),
% 0.20/0.52    inference(resolution,[],[f173,f48])).
% 0.20/0.52  fof(f173,plain,(
% 0.20/0.52    ( ! [X2,X3] : (~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X3,sK0) | m1_pre_topc(X2,X3) | ~r1_tarski(u1_struct_0(X2),u1_struct_0(X3))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f167,f36])).
% 0.20/0.52  fof(f167,plain,(
% 0.20/0.52    ( ! [X2,X3] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X3,sK0) | m1_pre_topc(X2,X3) | ~r1_tarski(u1_struct_0(X2),u1_struct_0(X3))) )),
% 0.20/0.52    inference(resolution,[],[f35,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (18969)------------------------------
% 0.20/0.52  % (18969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (18969)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (18969)Memory used [KB]: 3837
% 0.20/0.52  % (18969)Time elapsed: 0.119 s
% 0.20/0.52  % (18969)------------------------------
% 0.20/0.52  % (18969)------------------------------
% 0.20/0.52  % (18955)Success in time 0.172 s
%------------------------------------------------------------------------------
