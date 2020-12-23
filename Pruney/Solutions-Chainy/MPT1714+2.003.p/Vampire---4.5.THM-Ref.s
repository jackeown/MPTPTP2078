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
% DateTime   : Thu Dec  3 13:17:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 408 expanded)
%              Number of leaves         :    9 (  80 expanded)
%              Depth                    :   24
%              Number of atoms          :  278 (2804 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f248,plain,(
    $false ),
    inference(subsumption_resolution,[],[f247,f67])).

fof(f67,plain,(
    l1_pre_topc(sK1) ),
    inference(resolution,[],[f65,f35])).

fof(f35,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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

fof(f65,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f42,f38])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f247,plain,(
    ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f240,f41])).

fof(f41,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f240,plain,(
    ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f239,f66])).

fof(f66,plain,(
    l1_pre_topc(sK3) ),
    inference(resolution,[],[f65,f30])).

fof(f30,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f239,plain,
    ( ~ l1_struct_0(sK1)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f238,f41])).

fof(f238,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f237,f235])).

fof(f235,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(resolution,[],[f233,f28])).

fof(f28,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f233,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1) ),
    inference(resolution,[],[f232,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f232,plain,(
    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(duplicate_literal_removal,[],[f231])).

fof(f231,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(resolution,[],[f225,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
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

fof(f225,plain,(
    ! [X9] :
      ( ~ r2_hidden(sK4(u1_struct_0(sK3),X9),u1_struct_0(sK1))
      | r1_xboole_0(u1_struct_0(sK3),X9) ) ),
    inference(subsumption_resolution,[],[f224,f97])).

fof(f97,plain,(
    r1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f96,f66])).

fof(f96,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | r1_tsep_1(sK2,sK3) ),
    inference(resolution,[],[f93,f27])).

fof(f27,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f93,plain,(
    ! [X2] :
      ( ~ r1_tsep_1(X2,sK2)
      | r1_tsep_1(sK2,X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f90,f68])).

fof(f68,plain,(
    l1_pre_topc(sK2) ),
    inference(resolution,[],[f65,f33])).

fof(f33,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f89,f41])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f50,f41])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f224,plain,(
    ! [X9] :
      ( ~ r2_hidden(sK4(u1_struct_0(sK3),X9),u1_struct_0(sK1))
      | ~ r1_tsep_1(sK2,sK3)
      | r1_xboole_0(u1_struct_0(sK3),X9) ) ),
    inference(subsumption_resolution,[],[f216,f68])).

fof(f216,plain,(
    ! [X9] :
      ( ~ r2_hidden(sK4(u1_struct_0(sK3),X9),u1_struct_0(sK1))
      | ~ l1_pre_topc(sK2)
      | ~ r1_tsep_1(sK2,sK3)
      | r1_xboole_0(u1_struct_0(sK3),X9) ) ),
    inference(resolution,[],[f208,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(u1_struct_0(sK3),X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ r1_tsep_1(X1,sK3)
      | r1_xboole_0(u1_struct_0(sK3),X0) ) ),
    inference(resolution,[],[f117,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f117,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,u1_struct_0(sK3))
      | ~ r2_hidden(X6,u1_struct_0(X7))
      | ~ l1_pre_topc(X7)
      | ~ r1_tsep_1(X7,sK3) ) ),
    inference(resolution,[],[f113,f66])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(X0,X1) ) ),
    inference(resolution,[],[f110,f41])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X1,X0)
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f108,f41])).

fof(f108,plain,(
    ! [X4,X2,X3] :
      ( ~ l1_struct_0(X3)
      | ~ l1_struct_0(X2)
      | ~ r1_tsep_1(X3,X2)
      | ~ r2_hidden(X4,u1_struct_0(X2))
      | ~ r2_hidden(X4,u1_struct_0(X3)) ) ),
    inference(resolution,[],[f40,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f208,plain,(
    ! [X1] :
      ( r2_hidden(X1,u1_struct_0(sK2))
      | ~ r2_hidden(X1,u1_struct_0(sK1)) ) ),
    inference(superposition,[],[f63,f206])).

fof(f206,plain,(
    u1_struct_0(sK2) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f204,f33])).

fof(f204,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | u1_struct_0(sK2) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(resolution,[],[f201,f31])).

fof(f31,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f201,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(sK1,X1)
      | ~ m1_pre_topc(X1,sK0)
      | u1_struct_0(X1) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X1)) ) ),
    inference(resolution,[],[f193,f35])).

fof(f193,plain,(
    ! [X2,X3] :
      ( ~ m1_pre_topc(X3,sK0)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(X2,sK0)
      | u1_struct_0(X2) = k2_xboole_0(u1_struct_0(X3),u1_struct_0(X2)) ) ),
    inference(resolution,[],[f188,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f188,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK0)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f184,f37])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f184,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_pre_topc(X1,sK0)
      | ~ m1_pre_topc(X0,X1)
      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ) ),
    inference(resolution,[],[f44,f38])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f237,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | r1_tsep_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f236,f66])).

fof(f236,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | r1_tsep_1(sK1,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f233,f92])).

fof(f92,plain,(
    ! [X1] :
      ( ~ r1_tsep_1(X1,sK1)
      | r1_tsep_1(sK1,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f90,f67])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:50:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (17041)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.47  % (17041)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (17034)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.48  % (17022)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.49  % (17022)Refutation not found, incomplete strategy% (17022)------------------------------
% 0.21/0.49  % (17022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f248,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f247,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    l1_pre_topc(sK1)),
% 0.21/0.49    inference(resolution,[],[f65,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    m1_pre_topc(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3))) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f11])).
% 0.21/0.49  fof(f11,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 0.21/0.49    inference(resolution,[],[f42,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.49  fof(f247,plain,(
% 0.21/0.49    ~l1_pre_topc(sK1)),
% 0.21/0.49    inference(resolution,[],[f240,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.49  fof(f240,plain,(
% 0.21/0.49    ~l1_struct_0(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f239,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    l1_pre_topc(sK3)),
% 0.21/0.49    inference(resolution,[],[f65,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    m1_pre_topc(sK3,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f239,plain,(
% 0.21/0.49    ~l1_struct_0(sK1) | ~l1_pre_topc(sK3)),
% 0.21/0.49    inference(resolution,[],[f238,f41])).
% 0.21/0.49  fof(f238,plain,(
% 0.21/0.49    ~l1_struct_0(sK3) | ~l1_struct_0(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f237,f235])).
% 0.21/0.49  fof(f235,plain,(
% 0.21/0.49    ~l1_struct_0(sK3) | ~l1_struct_0(sK1) | ~r1_tsep_1(sK1,sK3)),
% 0.21/0.49    inference(resolution,[],[f233,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    r1_tsep_1(sK3,sK1) | ~l1_struct_0(sK3) | ~l1_struct_0(sK1)),
% 0.21/0.49    inference(resolution,[],[f232,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | r1_tsep_1(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f231])).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) | r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.21/0.49    inference(resolution,[],[f225,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.49    inference(rectify,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.49  fof(f225,plain,(
% 0.21/0.49    ( ! [X9] : (~r2_hidden(sK4(u1_struct_0(sK3),X9),u1_struct_0(sK1)) | r1_xboole_0(u1_struct_0(sK3),X9)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f224,f97])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    r1_tsep_1(sK2,sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f96,f66])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    r1_tsep_1(sK2,sK3) | ~l1_pre_topc(sK3)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f95])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    r1_tsep_1(sK2,sK3) | ~l1_pre_topc(sK3) | r1_tsep_1(sK2,sK3)),
% 0.21/0.49    inference(resolution,[],[f93,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ( ! [X2] : (~r1_tsep_1(X2,sK2) | r1_tsep_1(sK2,X2) | ~l1_pre_topc(X2)) )),
% 0.21/0.49    inference(resolution,[],[f90,f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    l1_pre_topc(sK2)),
% 0.21/0.49    inference(resolution,[],[f65,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    m1_pre_topc(sK2,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_pre_topc(X1) | r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(resolution,[],[f89,f41])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_struct_0(X0) | ~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_pre_topc(X1)) )),
% 0.21/0.49    inference(resolution,[],[f50,f41])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_struct_0(X1) | ~l1_struct_0(X0) | ~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    ( ! [X9] : (~r2_hidden(sK4(u1_struct_0(sK3),X9),u1_struct_0(sK1)) | ~r1_tsep_1(sK2,sK3) | r1_xboole_0(u1_struct_0(sK3),X9)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f216,f68])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    ( ! [X9] : (~r2_hidden(sK4(u1_struct_0(sK3),X9),u1_struct_0(sK1)) | ~l1_pre_topc(sK2) | ~r1_tsep_1(sK2,sK3) | r1_xboole_0(u1_struct_0(sK3),X9)) )),
% 0.21/0.49    inference(resolution,[],[f208,f124])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(sK4(u1_struct_0(sK3),X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~r1_tsep_1(X1,sK3) | r1_xboole_0(u1_struct_0(sK3),X0)) )),
% 0.21/0.49    inference(resolution,[],[f117,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    ( ! [X6,X7] : (~r2_hidden(X6,u1_struct_0(sK3)) | ~r2_hidden(X6,u1_struct_0(X7)) | ~l1_pre_topc(X7) | ~r1_tsep_1(X7,sK3)) )),
% 0.21/0.49    inference(resolution,[],[f113,f66])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(X1) | ~r2_hidden(X2,u1_struct_0(X1)) | ~r2_hidden(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~r1_tsep_1(X0,X1)) )),
% 0.21/0.49    inference(resolution,[],[f110,f41])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~r1_tsep_1(X1,X0) | ~r2_hidden(X2,u1_struct_0(X0)) | ~r2_hidden(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1)) )),
% 0.21/0.49    inference(resolution,[],[f108,f41])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    ( ! [X4,X2,X3] : (~l1_struct_0(X3) | ~l1_struct_0(X2) | ~r1_tsep_1(X3,X2) | ~r2_hidden(X4,u1_struct_0(X2)) | ~r2_hidden(X4,u1_struct_0(X3))) )),
% 0.21/0.49    inference(resolution,[],[f40,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | ~r1_tsep_1(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f208,plain,(
% 0.21/0.49    ( ! [X1] : (r2_hidden(X1,u1_struct_0(sK2)) | ~r2_hidden(X1,u1_struct_0(sK1))) )),
% 0.21/0.49    inference(superposition,[],[f63,f206])).
% 0.21/0.49  fof(f206,plain,(
% 0.21/0.49    u1_struct_0(sK2) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.21/0.49    inference(subsumption_resolution,[],[f204,f33])).
% 0.21/0.49  fof(f204,plain,(
% 0.21/0.49    ~m1_pre_topc(sK2,sK0) | u1_struct_0(sK2) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.21/0.49    inference(resolution,[],[f201,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    m1_pre_topc(sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f201,plain,(
% 0.21/0.49    ( ! [X1] : (~m1_pre_topc(sK1,X1) | ~m1_pre_topc(X1,sK0) | u1_struct_0(X1) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X1))) )),
% 0.21/0.49    inference(resolution,[],[f193,f35])).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~m1_pre_topc(X3,sK0) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X2,sK0) | u1_struct_0(X2) = k2_xboole_0(u1_struct_0(X3),u1_struct_0(X2))) )),
% 0.21/0.49    inference(resolution,[],[f188,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.49  fof(f188,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f184,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    v2_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,X1) | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))) )),
% 0.21/0.49    inference(resolution,[],[f44,f38])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.49  fof(f237,plain,(
% 0.21/0.49    ~l1_struct_0(sK3) | ~l1_struct_0(sK1) | r1_tsep_1(sK1,sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f236,f66])).
% 0.21/0.49  fof(f236,plain,(
% 0.21/0.49    ~l1_struct_0(sK3) | ~l1_struct_0(sK1) | r1_tsep_1(sK1,sK3) | ~l1_pre_topc(sK3)),
% 0.21/0.49    inference(resolution,[],[f233,f92])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    ( ! [X1] : (~r1_tsep_1(X1,sK1) | r1_tsep_1(sK1,X1) | ~l1_pre_topc(X1)) )),
% 0.21/0.49    inference(resolution,[],[f90,f67])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (17041)------------------------------
% 0.21/0.49  % (17041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (17041)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (17041)Memory used [KB]: 1791
% 0.21/0.49  % (17041)Time elapsed: 0.065 s
% 0.21/0.49  % (17041)------------------------------
% 0.21/0.49  % (17041)------------------------------
% 0.21/0.49  % (17021)Success in time 0.125 s
%------------------------------------------------------------------------------
