%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 303 expanded)
%              Number of leaves         :    5 (  51 expanded)
%              Depth                    :   35
%              Number of atoms          :  321 (1564 expanded)
%              Number of equality atoms :   41 ( 242 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f89,plain,(
    $false ),
    inference(subsumption_resolution,[],[f88,f20])).

fof(f20,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X1,X1)
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X1,X1)
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X1) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tmap_1)).

fof(f88,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f87,f21])).

fof(f21,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f87,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f85,f22])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f85,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f84,f18])).

fof(f18,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f84,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f83,f46])).

fof(f46,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(subsumption_resolution,[],[f45,f20])).

fof(f45,plain,
    ( v2_struct_0(sK0)
    | m1_pre_topc(sK1,sK1) ),
    inference(subsumption_resolution,[],[f44,f18])).

fof(f44,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK1,sK1) ),
    inference(subsumption_resolution,[],[f43,f17])).

fof(f17,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f43,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK1,sK1) ),
    inference(subsumption_resolution,[],[f42,f22])).

fof(f42,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK1,sK1) ),
    inference(subsumption_resolution,[],[f41,f21])).

fof(f41,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK1,sK1) ),
    inference(duplicate_literal_removal,[],[f40])).

fof(f40,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK1,sK1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_tsep_1(sK0,sK1,sK1) != k1_tsep_1(X0,X1,sK1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK1,X0)
      | v2_struct_0(X0)
      | m1_pre_topc(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f38,f17])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_tsep_1(sK0,sK1,sK1) != k1_tsep_1(X0,X1,sK1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X0)
      | v2_struct_0(X0)
      | m1_pre_topc(X1,sK1) ) ),
    inference(superposition,[],[f30,f36])).

fof(f36,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f35,f20])).

fof(f35,plain,
    ( v2_struct_0(sK0)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f34,f17])).

fof(f34,plain,
    ( v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f33,f22])).

fof(f33,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f32,f21])).

fof(f32,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK0,sK1,sK1) ),
    inference(resolution,[],[f23,f18])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tmap_1)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0)
      | m1_pre_topc(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

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
             => ( m1_pre_topc(X1,X2)
              <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tsep_1)).

fof(f83,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK1,X0)
      | ~ m1_pre_topc(sK1,sK1)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f82,f17])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X0)
      | ~ m1_pre_topc(sK1,sK1)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X0)
      | ~ m1_pre_topc(sK1,sK1)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f78,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X2,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ~ r1_tsep_1(X2,X1)
                & ~ r1_tsep_1(X1,X2) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ~ r1_tsep_1(X2,X1)
                & ~ r1_tsep_1(X1,X2) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).

fof(f78,plain,(
    r1_tsep_1(sK1,sK1) ),
    inference(subsumption_resolution,[],[f77,f20])).

fof(f77,plain,
    ( r1_tsep_1(sK1,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f76,f37])).

fof(f37,plain,(
    k2_tsep_1(sK0,sK1,sK1) != k1_tsep_1(sK0,sK1,sK1) ),
    inference(backward_demodulation,[],[f19,f36])).

fof(f19,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k2_tsep_1(sK0,sK1,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f76,plain,
    ( k2_tsep_1(sK0,sK1,sK1) = k1_tsep_1(sK0,sK1,sK1)
    | r1_tsep_1(sK1,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f75,f22])).

fof(f75,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_tsep_1(sK0,sK1,sK1) = k1_tsep_1(sK0,sK1,sK1)
    | r1_tsep_1(sK1,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f73,f21])).

fof(f73,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k2_tsep_1(sK0,sK1,sK1) = k1_tsep_1(sK0,sK1,sK1)
    | r1_tsep_1(sK1,sK1)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f72,f18])).

fof(f72,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(sK1,X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | k1_tsep_1(sK0,sK1,sK1) = k2_tsep_1(X1,sK1,sK1)
      | r1_tsep_1(sK1,sK1)
      | v2_struct_0(X1) ) ),
    inference(forward_demodulation,[],[f71,f36])).

fof(f71,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(sK1,X1)
      | r1_tsep_1(sK1,sK1)
      | v2_struct_0(X1)
      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(X1,sK1,sK1) ) ),
    inference(subsumption_resolution,[],[f67,f17])).

fof(f67,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X1)
      | r1_tsep_1(sK1,sK1)
      | v2_struct_0(X1)
      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(X1,sK1,sK1) ) ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X1)
      | r1_tsep_1(sK1,sK1)
      | v2_struct_0(X1)
      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(X1,sK1,sK1) ) ),
    inference(resolution,[],[f25,f46])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X2,X1)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k2_tsep_1(X0,X1,X2) )
                & ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(X0,X1,X2)
                  | ~ m1_pre_topc(X2,X1) )
                & ( m1_pre_topc(X1,X2)
                  | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X1,X2) )
                & ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X2)
                  | ~ m1_pre_topc(X1,X2) ) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X2,X1)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k2_tsep_1(X0,X1,X2) )
                & ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(X0,X1,X2)
                  | ~ m1_pre_topc(X2,X1) )
                & ( m1_pre_topc(X1,X2)
                  | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X1,X2) )
                & ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X2)
                  | ~ m1_pre_topc(X1,X2) ) )
              | r1_tsep_1(X1,X2)
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
             => ( ~ r1_tsep_1(X1,X2)
               => ( ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(X0,X1,X2)
                   => m1_pre_topc(X2,X1) )
                  & ( m1_pre_topc(X2,X1)
                   => g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(X0,X1,X2) )
                  & ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X2)
                   => m1_pre_topc(X1,X2) )
                  & ( m1_pre_topc(X1,X2)
                   => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tsep_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:47:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (28152)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.46  % (28144)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.46  % (28144)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f89,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(subsumption_resolution,[],[f88,f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ~v2_struct_0(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X1,X1) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f7])).
% 0.20/0.46  fof(f7,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X1,X1) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,negated_conjecture,(
% 0.20/0.46    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X1)))),
% 0.20/0.46    inference(negated_conjecture,[],[f5])).
% 0.20/0.46  fof(f5,conjecture,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X1)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tmap_1)).
% 0.20/0.46  fof(f88,plain,(
% 0.20/0.46    v2_struct_0(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f87,f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    v2_pre_topc(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f8])).
% 0.20/0.46  fof(f87,plain,(
% 0.20/0.46    ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f85,f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    l1_pre_topc(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f8])).
% 0.20/0.46  fof(f85,plain,(
% 0.20/0.46    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.46    inference(resolution,[],[f84,f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    m1_pre_topc(sK1,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f8])).
% 0.20/0.46  fof(f84,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f83,f46])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    m1_pre_topc(sK1,sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f45,f20])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    v2_struct_0(sK0) | m1_pre_topc(sK1,sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f44,f18])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | m1_pre_topc(sK1,sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f43,f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ~v2_struct_0(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f8])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | m1_pre_topc(sK1,sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f42,f22])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | m1_pre_topc(sK1,sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f41,f21])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | m1_pre_topc(sK1,sK1)),
% 0.20/0.46    inference(duplicate_literal_removal,[],[f40])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | m1_pre_topc(sK1,sK1)),
% 0.20/0.46    inference(equality_resolution,[],[f39])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_tsep_1(sK0,sK1,sK1) != k1_tsep_1(X0,X1,sK1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK1,X0) | v2_struct_0(X0) | m1_pre_topc(X1,sK1)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f38,f17])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_tsep_1(sK0,sK1,sK1) != k1_tsep_1(X0,X1,sK1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X0) | v2_struct_0(X0) | m1_pre_topc(X1,sK1)) )),
% 0.20/0.46    inference(superposition,[],[f30,f36])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK0,sK1,sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f35,f20])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    v2_struct_0(sK0) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK0,sK1,sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f34,f17])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    v2_struct_0(sK1) | v2_struct_0(sK0) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK0,sK1,sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f33,f22])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK0,sK1,sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f32,f21])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK0,sK1,sK1)),
% 0.20/0.46    inference(resolution,[],[f23,f18])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tmap_1)).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0) | m1_pre_topc(X1,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tsep_1)).
% 0.20/0.46  fof(f83,plain,(
% 0.20/0.46    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f82,f17])).
% 0.20/0.46  fof(f82,plain,(
% 0.20/0.46    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X0) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(duplicate_literal_removal,[],[f79])).
% 0.20/0.46  fof(f79,plain,(
% 0.20/0.46    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X0) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(resolution,[],[f78,f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_tsep_1(X2,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : ((~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (((~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)) | ~m1_pre_topc(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).
% 0.20/0.46  fof(f78,plain,(
% 0.20/0.46    r1_tsep_1(sK1,sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f77,f20])).
% 0.20/0.46  fof(f77,plain,(
% 0.20/0.46    r1_tsep_1(sK1,sK1) | v2_struct_0(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f76,f37])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    k2_tsep_1(sK0,sK1,sK1) != k1_tsep_1(sK0,sK1,sK1)),
% 0.20/0.46    inference(backward_demodulation,[],[f19,f36])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k2_tsep_1(sK0,sK1,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f8])).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    k2_tsep_1(sK0,sK1,sK1) = k1_tsep_1(sK0,sK1,sK1) | r1_tsep_1(sK1,sK1) | v2_struct_0(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f75,f22])).
% 0.20/0.46  fof(f75,plain,(
% 0.20/0.46    ~l1_pre_topc(sK0) | k2_tsep_1(sK0,sK1,sK1) = k1_tsep_1(sK0,sK1,sK1) | r1_tsep_1(sK1,sK1) | v2_struct_0(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f73,f21])).
% 0.20/0.46  fof(f73,plain,(
% 0.20/0.46    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | k2_tsep_1(sK0,sK1,sK1) = k1_tsep_1(sK0,sK1,sK1) | r1_tsep_1(sK1,sK1) | v2_struct_0(sK0)),
% 0.20/0.46    inference(resolution,[],[f72,f18])).
% 0.20/0.46  fof(f72,plain,(
% 0.20/0.46    ( ! [X1] : (~m1_pre_topc(sK1,X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | k1_tsep_1(sK0,sK1,sK1) = k2_tsep_1(X1,sK1,sK1) | r1_tsep_1(sK1,sK1) | v2_struct_0(X1)) )),
% 0.20/0.46    inference(forward_demodulation,[],[f71,f36])).
% 0.20/0.46  fof(f71,plain,(
% 0.20/0.46    ( ! [X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK1,X1) | r1_tsep_1(sK1,sK1) | v2_struct_0(X1) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(X1,sK1,sK1)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f67,f17])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    ( ! [X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X1) | r1_tsep_1(sK1,sK1) | v2_struct_0(X1) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(X1,sK1,sK1)) )),
% 0.20/0.46    inference(duplicate_literal_removal,[],[f66])).
% 0.20/0.46  fof(f66,plain,(
% 0.20/0.46    ( ! [X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X1) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X1) | r1_tsep_1(sK1,sK1) | v2_struct_0(X1) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(X1,sK1,sK1)) )),
% 0.20/0.46    inference(resolution,[],[f25,f46])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | r1_tsep_1(X1,X2) | v2_struct_0(X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(X0,X1,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X2,X1) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k2_tsep_1(X0,X1,X2)) & (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X1)) & (m1_pre_topc(X1,X2) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X1,X2)) & (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X2) | ~m1_pre_topc(X1,X2))) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X2,X1) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k2_tsep_1(X0,X1,X2)) & (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X1)) & (m1_pre_topc(X1,X2) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X1,X2)) & (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X2) | ~m1_pre_topc(X1,X2))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ((g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(X0,X1,X2) => m1_pre_topc(X2,X1)) & (m1_pre_topc(X2,X1) => g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(X0,X1,X2)) & (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X2) => m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X2)))))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tsep_1)).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (28144)------------------------------
% 0.20/0.46  % (28144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (28144)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (28144)Memory used [KB]: 6140
% 0.20/0.46  % (28144)Time elapsed: 0.059 s
% 0.20/0.46  % (28144)------------------------------
% 0.20/0.46  % (28144)------------------------------
% 0.20/0.47  % (28130)Success in time 0.11 s
%------------------------------------------------------------------------------
