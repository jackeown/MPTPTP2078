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
% DateTime   : Thu Dec  3 13:17:58 EST 2020

% Result     : Theorem 5.51s
% Output     : Refutation 5.51s
% Verified   : 
% Statistics : Number of formulae       :  190 (2478 expanded)
%              Number of leaves         :   18 ( 986 expanded)
%              Depth                    :   35
%              Number of atoms          :  792 (28267 expanded)
%              Number of equality atoms :   28 ( 158 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6473,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6469,f872])).

fof(f872,plain,(
    r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7)) ),
    inference(forward_demodulation,[],[f871,f513])).

fof(f513,plain,(
    u1_struct_0(sK8) = k2_struct_0(sK8) ),
    inference(resolution,[],[f489,f78])).

fof(f78,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f489,plain,(
    l1_struct_0(sK8) ),
    inference(resolution,[],[f395,f81])).

fof(f81,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f395,plain,(
    l1_pre_topc(sK8) ),
    inference(subsumption_resolution,[],[f379,f68])).

fof(f68,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ( ~ r1_tsep_1(sK8,sK6)
      | ~ r1_tsep_1(sK6,sK8) )
    & ( r1_tsep_1(sK8,sK7)
      | r1_tsep_1(sK7,sK8) )
    & m1_pre_topc(sK6,sK7)
    & m1_pre_topc(sK8,sK5)
    & ~ v2_struct_0(sK8)
    & m1_pre_topc(sK7,sK5)
    & ~ v2_struct_0(sK7)
    & m1_pre_topc(sK6,sK5)
    & ~ v2_struct_0(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f17,f46,f45,f44,f43])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ r1_tsep_1(X3,X1)
                      | ~ r1_tsep_1(X1,X3) )
                    & ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X2,X3) )
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK5)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK5)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK5)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ r1_tsep_1(X3,X1)
                  | ~ r1_tsep_1(X1,X3) )
                & ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X2,X3) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X3,sK5)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK5)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK5)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ r1_tsep_1(X3,sK6)
                | ~ r1_tsep_1(sK6,X3) )
              & ( r1_tsep_1(X3,X2)
                | r1_tsep_1(X2,X3) )
              & m1_pre_topc(sK6,X2)
              & m1_pre_topc(X3,sK5)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK5)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK6,sK5)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ r1_tsep_1(X3,sK6)
              | ~ r1_tsep_1(sK6,X3) )
            & ( r1_tsep_1(X3,X2)
              | r1_tsep_1(X2,X3) )
            & m1_pre_topc(sK6,X2)
            & m1_pre_topc(X3,sK5)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK5)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ~ r1_tsep_1(X3,sK6)
            | ~ r1_tsep_1(sK6,X3) )
          & ( r1_tsep_1(X3,sK7)
            | r1_tsep_1(sK7,X3) )
          & m1_pre_topc(sK6,sK7)
          & m1_pre_topc(X3,sK5)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK7,sK5)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X3] :
        ( ( ~ r1_tsep_1(X3,sK6)
          | ~ r1_tsep_1(sK6,X3) )
        & ( r1_tsep_1(X3,sK7)
          | r1_tsep_1(sK7,X3) )
        & m1_pre_topc(sK6,sK7)
        & m1_pre_topc(X3,sK5)
        & ~ v2_struct_0(X3) )
   => ( ( ~ r1_tsep_1(sK8,sK6)
        | ~ r1_tsep_1(sK6,sK8) )
      & ( r1_tsep_1(sK8,sK7)
        | r1_tsep_1(sK7,sK8) )
      & m1_pre_topc(sK6,sK7)
      & m1_pre_topc(sK8,sK5)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
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
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
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
                     => ( ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) )
                        | ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
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
                   => ( ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) )
                      | ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).

fof(f379,plain,
    ( l1_pre_topc(sK8)
    | ~ l1_pre_topc(sK5) ),
    inference(resolution,[],[f74,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f74,plain,(
    m1_pre_topc(sK8,sK5) ),
    inference(cnf_transformation,[],[f47])).

fof(f871,plain,(
    r1_xboole_0(u1_struct_0(sK8),k2_struct_0(sK7)) ),
    inference(forward_demodulation,[],[f538,f371])).

fof(f371,plain,(
    u1_struct_0(sK7) = k2_struct_0(sK7) ),
    inference(resolution,[],[f347,f78])).

fof(f347,plain,(
    l1_struct_0(sK7) ),
    inference(resolution,[],[f307,f81])).

fof(f307,plain,(
    l1_pre_topc(sK7) ),
    inference(subsumption_resolution,[],[f291,f68])).

fof(f291,plain,
    ( l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK5) ),
    inference(resolution,[],[f72,f97])).

fof(f72,plain,(
    m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f47])).

fof(f538,plain,(
    r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK7)) ),
    inference(subsumption_resolution,[],[f537,f489])).

fof(f537,plain,
    ( r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK7))
    | ~ l1_struct_0(sK8) ),
    inference(subsumption_resolution,[],[f536,f347])).

fof(f536,plain,
    ( r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK7))
    | ~ l1_struct_0(sK7)
    | ~ l1_struct_0(sK8) ),
    inference(resolution,[],[f532,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f532,plain,(
    r1_tsep_1(sK8,sK7) ),
    inference(subsumption_resolution,[],[f531,f347])).

fof(f531,plain,
    ( r1_tsep_1(sK8,sK7)
    | ~ l1_struct_0(sK7) ),
    inference(subsumption_resolution,[],[f529,f489])).

fof(f529,plain,
    ( r1_tsep_1(sK8,sK7)
    | ~ l1_struct_0(sK8)
    | ~ l1_struct_0(sK7) ),
    inference(resolution,[],[f526,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f526,plain,(
    r1_tsep_1(sK7,sK8) ),
    inference(subsumption_resolution,[],[f525,f489])).

fof(f525,plain,
    ( r1_tsep_1(sK7,sK8)
    | ~ l1_struct_0(sK8) ),
    inference(subsumption_resolution,[],[f524,f347])).

fof(f524,plain,
    ( r1_tsep_1(sK7,sK8)
    | ~ l1_struct_0(sK7)
    | ~ l1_struct_0(sK8) ),
    inference(duplicate_literal_removal,[],[f522])).

fof(f522,plain,
    ( r1_tsep_1(sK7,sK8)
    | r1_tsep_1(sK7,sK8)
    | ~ l1_struct_0(sK7)
    | ~ l1_struct_0(sK8) ),
    inference(resolution,[],[f76,f104])).

fof(f76,plain,
    ( r1_tsep_1(sK8,sK7)
    | r1_tsep_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f47])).

fof(f6469,plain,(
    ~ r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7)) ),
    inference(superposition,[],[f1391,f6410])).

fof(f6410,plain,(
    k2_struct_0(sK7) = k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f6408,f5098])).

fof(f5098,plain,(
    r1_tarski(k2_struct_0(sK7),k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6))) ),
    inference(forward_demodulation,[],[f5097,f371])).

fof(f5097,plain,(
    r1_tarski(k2_struct_0(sK7),k2_xboole_0(u1_struct_0(sK7),k2_struct_0(sK6))) ),
    inference(forward_demodulation,[],[f5096,f283])).

fof(f283,plain,(
    u1_struct_0(sK6) = k2_struct_0(sK6) ),
    inference(resolution,[],[f259,f78])).

fof(f259,plain,(
    l1_struct_0(sK6) ),
    inference(resolution,[],[f212,f81])).

fof(f212,plain,(
    l1_pre_topc(sK6) ),
    inference(subsumption_resolution,[],[f196,f68])).

fof(f196,plain,
    ( l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK5) ),
    inference(resolution,[],[f70,f97])).

fof(f70,plain,(
    m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f47])).

fof(f5096,plain,(
    r1_tarski(k2_struct_0(sK7),k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))) ),
    inference(subsumption_resolution,[],[f5095,f66])).

fof(f66,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f47])).

fof(f5095,plain,
    ( r1_tarski(k2_struct_0(sK7),k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)))
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f5094,f68])).

fof(f5094,plain,
    ( r1_tarski(k2_struct_0(sK7),k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)))
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f5093,f71])).

fof(f71,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f47])).

fof(f5093,plain,
    ( r1_tarski(k2_struct_0(sK7),k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)))
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f5092,f72])).

fof(f5092,plain,
    ( r1_tarski(k2_struct_0(sK7),k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)))
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f5091,f69])).

fof(f69,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f47])).

fof(f5091,plain,
    ( r1_tarski(k2_struct_0(sK7),k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)))
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f5090,f70])).

fof(f5090,plain,
    ( r1_tarski(k2_struct_0(sK7),k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)))
    | ~ m1_pre_topc(sK6,sK5)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f5089,f718])).

fof(f718,plain,(
    ~ v2_struct_0(k1_tsep_1(sK5,sK7,sK6)) ),
    inference(resolution,[],[f713,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X2,X1))
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
        & v1_pre_topc(k1_tsep_1(X0,X2,X1))
        & ~ v2_struct_0(k1_tsep_1(X0,X2,X1)) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP4(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP4(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f713,plain,(
    sP4(sK5,sK6,sK7) ),
    inference(subsumption_resolution,[],[f711,f72])).

fof(f711,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | sP4(sK5,sK6,sK7) ),
    inference(resolution,[],[f245,f71])).

fof(f245,plain,(
    ! [X14] :
      ( v2_struct_0(X14)
      | ~ m1_pre_topc(X14,sK5)
      | sP4(sK5,sK6,X14) ) ),
    inference(subsumption_resolution,[],[f244,f66])).

fof(f244,plain,(
    ! [X14] :
      ( sP4(sK5,sK6,X14)
      | ~ m1_pre_topc(X14,sK5)
      | v2_struct_0(X14)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f243,f68])).

fof(f243,plain,(
    ! [X14] :
      ( sP4(sK5,sK6,X14)
      | ~ m1_pre_topc(X14,sK5)
      | v2_struct_0(X14)
      | ~ l1_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f209,f69])).

fof(f209,plain,(
    ! [X14] :
      ( sP4(sK5,sK6,X14)
      | v2_struct_0(sK6)
      | ~ m1_pre_topc(X14,sK5)
      | v2_struct_0(X14)
      | ~ l1_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(resolution,[],[f70,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( sP4(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( sP4(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f35,f41])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f5089,plain,
    ( r1_tarski(k2_struct_0(sK7),k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)))
    | v2_struct_0(k1_tsep_1(sK5,sK7,sK6))
    | ~ m1_pre_topc(sK6,sK5)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f5088,f719])).

fof(f719,plain,(
    v1_pre_topc(k1_tsep_1(sK5,sK7,sK6)) ),
    inference(resolution,[],[f713,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X2,X1))
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f5088,plain,
    ( r1_tarski(k2_struct_0(sK7),k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)))
    | ~ v1_pre_topc(k1_tsep_1(sK5,sK7,sK6))
    | v2_struct_0(k1_tsep_1(sK5,sK7,sK6))
    | ~ m1_pre_topc(sK6,sK5)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f5078,f720])).

fof(f720,plain,(
    m1_pre_topc(k1_tsep_1(sK5,sK7,sK6),sK5) ),
    inference(resolution,[],[f713,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f5078,plain,
    ( r1_tarski(k2_struct_0(sK7),k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)))
    | ~ m1_pre_topc(k1_tsep_1(sK5,sK7,sK6),sK5)
    | ~ v1_pre_topc(k1_tsep_1(sK5,sK7,sK6))
    | v2_struct_0(k1_tsep_1(sK5,sK7,sK6))
    | ~ m1_pre_topc(sK6,sK5)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5) ),
    inference(superposition,[],[f3609,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k1_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k1_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).

fof(f3609,plain,(
    r1_tarski(k2_struct_0(sK7),u1_struct_0(k1_tsep_1(sK5,sK7,sK6))) ),
    inference(subsumption_resolution,[],[f3601,f720])).

fof(f3601,plain,
    ( r1_tarski(k2_struct_0(sK7),u1_struct_0(k1_tsep_1(sK5,sK7,sK6)))
    | ~ m1_pre_topc(k1_tsep_1(sK5,sK7,sK6),sK5) ),
    inference(resolution,[],[f1938,f1084])).

fof(f1084,plain,(
    m1_pre_topc(sK7,k1_tsep_1(sK5,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f1081,f72])).

fof(f1081,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | m1_pre_topc(sK7,k1_tsep_1(sK5,sK7,sK6)) ),
    inference(resolution,[],[f220,f71])).

fof(f220,plain,(
    ! [X1] :
      ( v2_struct_0(X1)
      | ~ m1_pre_topc(X1,sK5)
      | m1_pre_topc(X1,k1_tsep_1(sK5,X1,sK6)) ) ),
    inference(subsumption_resolution,[],[f219,f66])).

fof(f219,plain,(
    ! [X1] :
      ( m1_pre_topc(X1,k1_tsep_1(sK5,X1,sK6))
      | ~ m1_pre_topc(X1,sK5)
      | v2_struct_0(X1)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f218,f67])).

fof(f67,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f47])).

fof(f218,plain,(
    ! [X1] :
      ( m1_pre_topc(X1,k1_tsep_1(sK5,X1,sK6))
      | ~ m1_pre_topc(X1,sK5)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f217,f68])).

fof(f217,plain,(
    ! [X1] :
      ( m1_pre_topc(X1,k1_tsep_1(sK5,X1,sK6))
      | ~ m1_pre_topc(X1,sK5)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f198,f69])).

fof(f198,plain,(
    ! [X1] :
      ( m1_pre_topc(X1,k1_tsep_1(sK5,X1,sK6))
      | v2_struct_0(sK6)
      | ~ m1_pre_topc(X1,sK5)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(resolution,[],[f70,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tsep_1)).

fof(f1938,plain,(
    ! [X10] :
      ( ~ m1_pre_topc(sK7,X10)
      | r1_tarski(k2_struct_0(sK7),u1_struct_0(X10))
      | ~ m1_pre_topc(X10,sK5) ) ),
    inference(forward_demodulation,[],[f332,f371])).

fof(f332,plain,(
    ! [X10] :
      ( r1_tarski(u1_struct_0(sK7),u1_struct_0(X10))
      | ~ m1_pre_topc(sK7,X10)
      | ~ m1_pre_topc(X10,sK5) ) ),
    inference(subsumption_resolution,[],[f331,f67])).

fof(f331,plain,(
    ! [X10] :
      ( r1_tarski(u1_struct_0(sK7),u1_struct_0(X10))
      | ~ m1_pre_topc(sK7,X10)
      | ~ m1_pre_topc(X10,sK5)
      | ~ v2_pre_topc(sK5) ) ),
    inference(subsumption_resolution,[],[f300,f68])).

fof(f300,plain,(
    ! [X10] :
      ( r1_tarski(u1_struct_0(sK7),u1_struct_0(X10))
      | ~ m1_pre_topc(sK7,X10)
      | ~ m1_pre_topc(X10,sK5)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5) ) ),
    inference(resolution,[],[f72,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f30])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f6408,plain,
    ( k2_struct_0(sK7) = k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6))
    | ~ r1_tarski(k2_struct_0(sK7),k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6))) ),
    inference(resolution,[],[f6370,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
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

fof(f6370,plain,(
    r1_tarski(k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6)),k2_struct_0(sK7)) ),
    inference(forward_demodulation,[],[f6369,f371])).

fof(f6369,plain,(
    r1_tarski(k2_xboole_0(u1_struct_0(sK7),k2_struct_0(sK6)),k2_struct_0(sK7)) ),
    inference(forward_demodulation,[],[f6368,f283])).

fof(f6368,plain,(
    r1_tarski(k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)),k2_struct_0(sK7)) ),
    inference(subsumption_resolution,[],[f6367,f307])).

fof(f6367,plain,
    ( r1_tarski(k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)),k2_struct_0(sK7))
    | ~ l1_pre_topc(sK7) ),
    inference(subsumption_resolution,[],[f6366,f71])).

fof(f6366,plain,
    ( r1_tarski(k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)),k2_struct_0(sK7))
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(subsumption_resolution,[],[f6365,f3461])).

fof(f3461,plain,(
    m1_pre_topc(sK7,sK7) ),
    inference(subsumption_resolution,[],[f3460,f72])).

fof(f3460,plain,
    ( m1_pre_topc(sK7,sK7)
    | ~ m1_pre_topc(sK7,sK5) ),
    inference(subsumption_resolution,[],[f3457,f118])).

fof(f118,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f3457,plain,
    ( ~ r1_tarski(k2_struct_0(sK7),k2_struct_0(sK7))
    | m1_pre_topc(sK7,sK7)
    | ~ m1_pre_topc(sK7,sK5) ),
    inference(superposition,[],[f1670,f371])).

fof(f1670,plain,(
    ! [X8] :
      ( ~ r1_tarski(k2_struct_0(sK7),u1_struct_0(X8))
      | m1_pre_topc(sK7,X8)
      | ~ m1_pre_topc(X8,sK5) ) ),
    inference(forward_demodulation,[],[f328,f371])).

fof(f328,plain,(
    ! [X8] :
      ( m1_pre_topc(sK7,X8)
      | ~ r1_tarski(u1_struct_0(sK7),u1_struct_0(X8))
      | ~ m1_pre_topc(X8,sK5) ) ),
    inference(subsumption_resolution,[],[f327,f67])).

fof(f327,plain,(
    ! [X8] :
      ( m1_pre_topc(sK7,X8)
      | ~ r1_tarski(u1_struct_0(sK7),u1_struct_0(X8))
      | ~ m1_pre_topc(X8,sK5)
      | ~ v2_pre_topc(sK5) ) ),
    inference(subsumption_resolution,[],[f298,f68])).

fof(f298,plain,(
    ! [X8] :
      ( m1_pre_topc(sK7,X8)
      | ~ r1_tarski(u1_struct_0(sK7),u1_struct_0(X8))
      | ~ m1_pre_topc(X8,sK5)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5) ) ),
    inference(resolution,[],[f72,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f6365,plain,
    ( r1_tarski(k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)),k2_struct_0(sK7))
    | ~ m1_pre_topc(sK7,sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(subsumption_resolution,[],[f6364,f69])).

fof(f6364,plain,
    ( r1_tarski(k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)),k2_struct_0(sK7))
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK7,sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(subsumption_resolution,[],[f6363,f75])).

fof(f75,plain,(
    m1_pre_topc(sK6,sK7) ),
    inference(cnf_transformation,[],[f47])).

fof(f6363,plain,
    ( r1_tarski(k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)),k2_struct_0(sK7))
    | ~ m1_pre_topc(sK6,sK7)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK7,sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(subsumption_resolution,[],[f6362,f4508])).

fof(f4508,plain,(
    ~ v2_struct_0(k1_tsep_1(sK7,sK7,sK6)) ),
    inference(resolution,[],[f4507,f111])).

fof(f4507,plain,(
    sP4(sK7,sK6,sK7) ),
    inference(subsumption_resolution,[],[f895,f3461])).

fof(f895,plain,
    ( ~ m1_pre_topc(sK7,sK7)
    | sP4(sK7,sK6,sK7) ),
    inference(resolution,[],[f482,f71])).

fof(f482,plain,(
    ! [X14] :
      ( v2_struct_0(X14)
      | ~ m1_pre_topc(X14,sK7)
      | sP4(sK7,sK6,X14) ) ),
    inference(subsumption_resolution,[],[f481,f71])).

fof(f481,plain,(
    ! [X14] :
      ( sP4(sK7,sK6,X14)
      | ~ m1_pre_topc(X14,sK7)
      | v2_struct_0(X14)
      | v2_struct_0(sK7) ) ),
    inference(subsumption_resolution,[],[f480,f307])).

fof(f480,plain,(
    ! [X14] :
      ( sP4(sK7,sK6,X14)
      | ~ m1_pre_topc(X14,sK7)
      | v2_struct_0(X14)
      | ~ l1_pre_topc(sK7)
      | v2_struct_0(sK7) ) ),
    inference(subsumption_resolution,[],[f449,f69])).

fof(f449,plain,(
    ! [X14] :
      ( sP4(sK7,sK6,X14)
      | v2_struct_0(sK6)
      | ~ m1_pre_topc(X14,sK7)
      | v2_struct_0(X14)
      | ~ l1_pre_topc(sK7)
      | v2_struct_0(sK7) ) ),
    inference(resolution,[],[f75,f114])).

fof(f6362,plain,
    ( r1_tarski(k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)),k2_struct_0(sK7))
    | v2_struct_0(k1_tsep_1(sK7,sK7,sK6))
    | ~ m1_pre_topc(sK6,sK7)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK7,sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(subsumption_resolution,[],[f6361,f4509])).

fof(f4509,plain,(
    v1_pre_topc(k1_tsep_1(sK7,sK7,sK6)) ),
    inference(resolution,[],[f4507,f112])).

fof(f6361,plain,
    ( r1_tarski(k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)),k2_struct_0(sK7))
    | ~ v1_pre_topc(k1_tsep_1(sK7,sK7,sK6))
    | v2_struct_0(k1_tsep_1(sK7,sK7,sK6))
    | ~ m1_pre_topc(sK6,sK7)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK7,sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(subsumption_resolution,[],[f6359,f4510])).

fof(f4510,plain,(
    m1_pre_topc(k1_tsep_1(sK7,sK7,sK6),sK7) ),
    inference(resolution,[],[f4507,f113])).

fof(f6359,plain,
    ( r1_tarski(k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)),k2_struct_0(sK7))
    | ~ m1_pre_topc(k1_tsep_1(sK7,sK7,sK6),sK7)
    | ~ v1_pre_topc(k1_tsep_1(sK7,sK7,sK6))
    | v2_struct_0(k1_tsep_1(sK7,sK7,sK6))
    | ~ m1_pre_topc(sK6,sK7)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK7,sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(duplicate_literal_removal,[],[f6357])).

fof(f6357,plain,
    ( r1_tarski(k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)),k2_struct_0(sK7))
    | ~ m1_pre_topc(k1_tsep_1(sK7,sK7,sK6),sK7)
    | ~ v1_pre_topc(k1_tsep_1(sK7,sK7,sK6))
    | v2_struct_0(k1_tsep_1(sK7,sK7,sK6))
    | ~ m1_pre_topc(sK6,sK7)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK7,sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7)
    | v2_struct_0(sK7) ),
    inference(superposition,[],[f6096,f116])).

fof(f6096,plain,(
    r1_tarski(u1_struct_0(k1_tsep_1(sK7,sK7,sK6)),k2_struct_0(sK7)) ),
    inference(resolution,[],[f3521,f4510])).

fof(f3521,plain,(
    ! [X11] :
      ( ~ m1_pre_topc(X11,sK7)
      | r1_tarski(u1_struct_0(X11),k2_struct_0(sK7)) ) ),
    inference(forward_demodulation,[],[f3520,f371])).

fof(f3520,plain,(
    ! [X11] :
      ( r1_tarski(u1_struct_0(X11),u1_struct_0(sK7))
      | ~ m1_pre_topc(X11,sK7) ) ),
    inference(subsumption_resolution,[],[f3519,f326])).

fof(f326,plain,(
    v2_pre_topc(sK7) ),
    inference(subsumption_resolution,[],[f325,f67])).

fof(f325,plain,
    ( v2_pre_topc(sK7)
    | ~ v2_pre_topc(sK5) ),
    inference(subsumption_resolution,[],[f297,f68])).

fof(f297,plain,
    ( v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(resolution,[],[f72,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f3519,plain,(
    ! [X11] :
      ( r1_tarski(u1_struct_0(X11),u1_struct_0(sK7))
      | ~ m1_pre_topc(X11,sK7)
      | ~ v2_pre_topc(sK7) ) ),
    inference(subsumption_resolution,[],[f3489,f307])).

fof(f3489,plain,(
    ! [X11] :
      ( r1_tarski(u1_struct_0(X11),u1_struct_0(sK7))
      | ~ m1_pre_topc(X11,sK7)
      | ~ l1_pre_topc(sK7)
      | ~ v2_pre_topc(sK7) ) ),
    inference(duplicate_literal_removal,[],[f3478])).

fof(f3478,plain,(
    ! [X11] :
      ( r1_tarski(u1_struct_0(X11),u1_struct_0(sK7))
      | ~ m1_pre_topc(X11,sK7)
      | ~ m1_pre_topc(X11,sK7)
      | ~ l1_pre_topc(sK7)
      | ~ v2_pre_topc(sK7) ) ),
    inference(resolution,[],[f3461,f103])).

fof(f1391,plain,(
    ! [X1] : ~ r1_xboole_0(k2_struct_0(sK8),k2_xboole_0(X1,k2_struct_0(sK6))) ),
    inference(resolution,[],[f883,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f883,plain,(
    ~ r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6)) ),
    inference(forward_demodulation,[],[f882,f513])).

fof(f882,plain,(
    ~ r1_xboole_0(u1_struct_0(sK8),k2_struct_0(sK6)) ),
    inference(forward_demodulation,[],[f563,f283])).

fof(f563,plain,(
    ~ r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f562,f489])).

fof(f562,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK6))
    | ~ l1_struct_0(sK8) ),
    inference(subsumption_resolution,[],[f561,f259])).

fof(f561,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK6))
    | ~ l1_struct_0(sK6)
    | ~ l1_struct_0(sK8) ),
    inference(resolution,[],[f557,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X0,X1)
      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f557,plain,(
    ~ r1_tsep_1(sK8,sK6) ),
    inference(subsumption_resolution,[],[f556,f489])).

fof(f556,plain,
    ( ~ r1_tsep_1(sK8,sK6)
    | ~ l1_struct_0(sK8) ),
    inference(subsumption_resolution,[],[f554,f259])).

fof(f554,plain,
    ( ~ r1_tsep_1(sK8,sK6)
    | ~ l1_struct_0(sK6)
    | ~ l1_struct_0(sK8) ),
    inference(resolution,[],[f551,f104])).

fof(f551,plain,(
    ~ r1_tsep_1(sK6,sK8) ),
    inference(subsumption_resolution,[],[f550,f259])).

fof(f550,plain,
    ( ~ r1_tsep_1(sK6,sK8)
    | ~ l1_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f549,f489])).

fof(f549,plain,
    ( ~ r1_tsep_1(sK6,sK8)
    | ~ l1_struct_0(sK8)
    | ~ l1_struct_0(sK6) ),
    inference(duplicate_literal_removal,[],[f547])).

fof(f547,plain,
    ( ~ r1_tsep_1(sK6,sK8)
    | ~ r1_tsep_1(sK6,sK8)
    | ~ l1_struct_0(sK8)
    | ~ l1_struct_0(sK6) ),
    inference(resolution,[],[f77,f104])).

fof(f77,plain,
    ( ~ r1_tsep_1(sK8,sK6)
    | ~ r1_tsep_1(sK6,sK8) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:18:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (21653)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (21648)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (21654)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.53  % (21672)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.53  % (21669)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  % (21667)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.54  % (21663)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.54  % (21651)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.54  % (21656)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.72/0.59  % (21674)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.72/0.59  % (21666)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.72/0.59  % (21655)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.72/0.60  % (21649)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.72/0.60  % (21665)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.72/0.60  % (21647)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.72/0.61  % (21657)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.72/0.61  % (21647)Refutation not found, incomplete strategy% (21647)------------------------------
% 1.72/0.61  % (21647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.61  % (21647)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.61  
% 1.72/0.61  % (21647)Memory used [KB]: 10618
% 1.72/0.61  % (21647)Time elapsed: 0.163 s
% 1.72/0.61  % (21647)------------------------------
% 1.72/0.61  % (21647)------------------------------
% 1.72/0.61  % (21659)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.72/0.62  % (21658)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.72/0.63  % (21650)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.72/0.65  % (21668)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 2.31/0.66  % (21671)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 2.31/0.67  % (21673)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 2.46/0.67  % (21652)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 2.46/0.68  % (21661)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 2.46/0.69  % (21661)Refutation not found, incomplete strategy% (21661)------------------------------
% 2.46/0.69  % (21661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.46/0.69  % (21661)Termination reason: Refutation not found, incomplete strategy
% 2.46/0.69  
% 2.46/0.69  % (21661)Memory used [KB]: 6140
% 2.46/0.69  % (21661)Time elapsed: 0.250 s
% 2.46/0.69  % (21661)------------------------------
% 2.46/0.69  % (21661)------------------------------
% 2.46/0.69  % (21664)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 2.46/0.70  % (21670)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 2.96/0.75  % (21656)Refutation not found, incomplete strategy% (21656)------------------------------
% 2.96/0.75  % (21656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.96/0.75  % (21656)Termination reason: Refutation not found, incomplete strategy
% 2.96/0.75  
% 2.96/0.75  % (21656)Memory used [KB]: 6140
% 2.96/0.75  % (21656)Time elapsed: 0.313 s
% 2.96/0.75  % (21656)------------------------------
% 2.96/0.75  % (21656)------------------------------
% 4.72/0.97  % (21663)Time limit reached!
% 4.72/0.97  % (21663)------------------------------
% 4.72/0.97  % (21663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.72/0.97  % (21663)Termination reason: Time limit
% 4.72/0.97  
% 4.72/0.97  % (21663)Memory used [KB]: 7547
% 4.72/0.97  % (21663)Time elapsed: 0.521 s
% 4.72/0.97  % (21663)------------------------------
% 4.72/0.97  % (21663)------------------------------
% 5.51/1.06  % (21653)Time limit reached!
% 5.51/1.06  % (21653)------------------------------
% 5.51/1.06  % (21653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.51/1.06  % (21653)Termination reason: Time limit
% 5.51/1.06  % (21653)Termination phase: Saturation
% 5.51/1.06  
% 5.51/1.06  % (21653)Memory used [KB]: 15735
% 5.51/1.06  % (21653)Time elapsed: 0.600 s
% 5.51/1.06  % (21653)------------------------------
% 5.51/1.06  % (21653)------------------------------
% 5.51/1.10  % (21655)Refutation found. Thanks to Tanya!
% 5.51/1.10  % SZS status Theorem for theBenchmark
% 5.51/1.10  % SZS output start Proof for theBenchmark
% 5.51/1.10  fof(f6473,plain,(
% 5.51/1.10    $false),
% 5.51/1.10    inference(subsumption_resolution,[],[f6469,f872])).
% 5.51/1.10  fof(f872,plain,(
% 5.51/1.10    r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7))),
% 5.51/1.10    inference(forward_demodulation,[],[f871,f513])).
% 5.51/1.10  fof(f513,plain,(
% 5.51/1.10    u1_struct_0(sK8) = k2_struct_0(sK8)),
% 5.51/1.10    inference(resolution,[],[f489,f78])).
% 5.51/1.10  fof(f78,plain,(
% 5.51/1.10    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 5.51/1.10    inference(cnf_transformation,[],[f18])).
% 5.51/1.10  fof(f18,plain,(
% 5.51/1.10    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 5.51/1.10    inference(ennf_transformation,[],[f4])).
% 5.51/1.10  fof(f4,axiom,(
% 5.51/1.10    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 5.51/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 5.51/1.10  fof(f489,plain,(
% 5.51/1.10    l1_struct_0(sK8)),
% 5.51/1.10    inference(resolution,[],[f395,f81])).
% 5.51/1.10  fof(f81,plain,(
% 5.51/1.10    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 5.51/1.10    inference(cnf_transformation,[],[f20])).
% 5.51/1.10  fof(f20,plain,(
% 5.51/1.10    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 5.51/1.10    inference(ennf_transformation,[],[f6])).
% 5.51/1.10  fof(f6,axiom,(
% 5.51/1.10    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 5.51/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 5.51/1.10  fof(f395,plain,(
% 5.51/1.10    l1_pre_topc(sK8)),
% 5.51/1.10    inference(subsumption_resolution,[],[f379,f68])).
% 5.51/1.10  fof(f68,plain,(
% 5.51/1.10    l1_pre_topc(sK5)),
% 5.51/1.10    inference(cnf_transformation,[],[f47])).
% 5.51/1.10  fof(f47,plain,(
% 5.51/1.10    ((((~r1_tsep_1(sK8,sK6) | ~r1_tsep_1(sK6,sK8)) & (r1_tsep_1(sK8,sK7) | r1_tsep_1(sK7,sK8)) & m1_pre_topc(sK6,sK7) & m1_pre_topc(sK8,sK5) & ~v2_struct_0(sK8)) & m1_pre_topc(sK7,sK5) & ~v2_struct_0(sK7)) & m1_pre_topc(sK6,sK5) & ~v2_struct_0(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 5.51/1.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f17,f46,f45,f44,f43])).
% 5.51/1.10  fof(f43,plain,(
% 5.51/1.10    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK5) & ~v2_struct_0(X1)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 5.51/1.10    introduced(choice_axiom,[])).
% 5.51/1.10  fof(f44,plain,(
% 5.51/1.10    ? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK5) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((~r1_tsep_1(X3,sK6) | ~r1_tsep_1(sK6,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(sK6,X2) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & ~v2_struct_0(X2)) & m1_pre_topc(sK6,sK5) & ~v2_struct_0(sK6))),
% 5.51/1.10    introduced(choice_axiom,[])).
% 5.51/1.10  fof(f45,plain,(
% 5.51/1.10    ? [X2] : (? [X3] : ((~r1_tsep_1(X3,sK6) | ~r1_tsep_1(sK6,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(sK6,X2) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & ~v2_struct_0(X2)) => (? [X3] : ((~r1_tsep_1(X3,sK6) | ~r1_tsep_1(sK6,X3)) & (r1_tsep_1(X3,sK7) | r1_tsep_1(sK7,X3)) & m1_pre_topc(sK6,sK7) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(sK7,sK5) & ~v2_struct_0(sK7))),
% 5.51/1.10    introduced(choice_axiom,[])).
% 5.51/1.10  fof(f46,plain,(
% 5.51/1.10    ? [X3] : ((~r1_tsep_1(X3,sK6) | ~r1_tsep_1(sK6,X3)) & (r1_tsep_1(X3,sK7) | r1_tsep_1(sK7,X3)) & m1_pre_topc(sK6,sK7) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) => ((~r1_tsep_1(sK8,sK6) | ~r1_tsep_1(sK6,sK8)) & (r1_tsep_1(sK8,sK7) | r1_tsep_1(sK7,sK8)) & m1_pre_topc(sK6,sK7) & m1_pre_topc(sK8,sK5) & ~v2_struct_0(sK8))),
% 5.51/1.10    introduced(choice_axiom,[])).
% 5.51/1.10  fof(f17,plain,(
% 5.51/1.10    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 5.51/1.10    inference(flattening,[],[f16])).
% 5.51/1.10  fof(f16,plain,(
% 5.51/1.10    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3))) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 5.51/1.10    inference(ennf_transformation,[],[f15])).
% 5.51/1.10  fof(f15,negated_conjecture,(
% 5.51/1.10    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 5.51/1.10    inference(negated_conjecture,[],[f14])).
% 5.51/1.10  fof(f14,conjecture,(
% 5.51/1.10    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 5.51/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).
% 5.51/1.10  fof(f379,plain,(
% 5.51/1.10    l1_pre_topc(sK8) | ~l1_pre_topc(sK5)),
% 5.51/1.10    inference(resolution,[],[f74,f97])).
% 5.51/1.10  fof(f97,plain,(
% 5.51/1.10    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 5.51/1.10    inference(cnf_transformation,[],[f22])).
% 5.51/1.10  fof(f22,plain,(
% 5.51/1.10    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 5.51/1.10    inference(ennf_transformation,[],[f7])).
% 5.51/1.10  fof(f7,axiom,(
% 5.51/1.10    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 5.51/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 5.51/1.10  fof(f74,plain,(
% 5.51/1.10    m1_pre_topc(sK8,sK5)),
% 5.51/1.10    inference(cnf_transformation,[],[f47])).
% 5.51/1.10  fof(f871,plain,(
% 5.51/1.10    r1_xboole_0(u1_struct_0(sK8),k2_struct_0(sK7))),
% 5.51/1.10    inference(forward_demodulation,[],[f538,f371])).
% 5.51/1.10  fof(f371,plain,(
% 5.51/1.10    u1_struct_0(sK7) = k2_struct_0(sK7)),
% 5.51/1.10    inference(resolution,[],[f347,f78])).
% 5.51/1.10  fof(f347,plain,(
% 5.51/1.10    l1_struct_0(sK7)),
% 5.51/1.10    inference(resolution,[],[f307,f81])).
% 5.51/1.10  fof(f307,plain,(
% 5.51/1.10    l1_pre_topc(sK7)),
% 5.51/1.10    inference(subsumption_resolution,[],[f291,f68])).
% 5.51/1.10  fof(f291,plain,(
% 5.51/1.10    l1_pre_topc(sK7) | ~l1_pre_topc(sK5)),
% 5.51/1.10    inference(resolution,[],[f72,f97])).
% 5.51/1.10  fof(f72,plain,(
% 5.51/1.10    m1_pre_topc(sK7,sK5)),
% 5.51/1.10    inference(cnf_transformation,[],[f47])).
% 5.51/1.10  fof(f538,plain,(
% 5.51/1.10    r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK7))),
% 5.51/1.10    inference(subsumption_resolution,[],[f537,f489])).
% 5.51/1.10  fof(f537,plain,(
% 5.51/1.10    r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK7)) | ~l1_struct_0(sK8)),
% 5.51/1.10    inference(subsumption_resolution,[],[f536,f347])).
% 5.51/1.10  fof(f536,plain,(
% 5.51/1.10    r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK7)) | ~l1_struct_0(sK7) | ~l1_struct_0(sK8)),
% 5.51/1.10    inference(resolution,[],[f532,f79])).
% 5.51/1.10  fof(f79,plain,(
% 5.51/1.10    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 5.51/1.10    inference(cnf_transformation,[],[f48])).
% 5.51/1.10  fof(f48,plain,(
% 5.51/1.10    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 5.51/1.10    inference(nnf_transformation,[],[f19])).
% 5.51/1.10  fof(f19,plain,(
% 5.51/1.10    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 5.51/1.10    inference(ennf_transformation,[],[f9])).
% 5.51/1.10  fof(f9,axiom,(
% 5.51/1.10    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 5.51/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).
% 5.51/1.10  fof(f532,plain,(
% 5.51/1.10    r1_tsep_1(sK8,sK7)),
% 5.51/1.10    inference(subsumption_resolution,[],[f531,f347])).
% 5.51/1.10  fof(f531,plain,(
% 5.51/1.10    r1_tsep_1(sK8,sK7) | ~l1_struct_0(sK7)),
% 5.51/1.10    inference(subsumption_resolution,[],[f529,f489])).
% 5.51/1.10  fof(f529,plain,(
% 5.51/1.10    r1_tsep_1(sK8,sK7) | ~l1_struct_0(sK8) | ~l1_struct_0(sK7)),
% 5.51/1.10    inference(resolution,[],[f526,f104])).
% 5.51/1.10  fof(f104,plain,(
% 5.51/1.10    ( ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 5.51/1.10    inference(cnf_transformation,[],[f32])).
% 5.51/1.10  fof(f32,plain,(
% 5.51/1.10    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 5.51/1.10    inference(flattening,[],[f31])).
% 5.51/1.10  fof(f31,plain,(
% 5.51/1.10    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 5.51/1.10    inference(ennf_transformation,[],[f11])).
% 5.51/1.10  fof(f11,axiom,(
% 5.51/1.10    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 5.51/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 5.51/1.10  fof(f526,plain,(
% 5.51/1.10    r1_tsep_1(sK7,sK8)),
% 5.51/1.10    inference(subsumption_resolution,[],[f525,f489])).
% 5.51/1.10  fof(f525,plain,(
% 5.51/1.10    r1_tsep_1(sK7,sK8) | ~l1_struct_0(sK8)),
% 5.51/1.10    inference(subsumption_resolution,[],[f524,f347])).
% 5.51/1.10  fof(f524,plain,(
% 5.51/1.10    r1_tsep_1(sK7,sK8) | ~l1_struct_0(sK7) | ~l1_struct_0(sK8)),
% 5.51/1.10    inference(duplicate_literal_removal,[],[f522])).
% 5.51/1.10  fof(f522,plain,(
% 5.51/1.10    r1_tsep_1(sK7,sK8) | r1_tsep_1(sK7,sK8) | ~l1_struct_0(sK7) | ~l1_struct_0(sK8)),
% 5.51/1.10    inference(resolution,[],[f76,f104])).
% 5.51/1.10  fof(f76,plain,(
% 5.51/1.10    r1_tsep_1(sK8,sK7) | r1_tsep_1(sK7,sK8)),
% 5.51/1.10    inference(cnf_transformation,[],[f47])).
% 5.51/1.10  fof(f6469,plain,(
% 5.51/1.10    ~r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7))),
% 5.51/1.10    inference(superposition,[],[f1391,f6410])).
% 5.51/1.10  fof(f6410,plain,(
% 5.51/1.10    k2_struct_0(sK7) = k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6))),
% 5.51/1.10    inference(subsumption_resolution,[],[f6408,f5098])).
% 5.51/1.10  fof(f5098,plain,(
% 5.51/1.10    r1_tarski(k2_struct_0(sK7),k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6)))),
% 5.51/1.10    inference(forward_demodulation,[],[f5097,f371])).
% 5.51/1.10  fof(f5097,plain,(
% 5.51/1.10    r1_tarski(k2_struct_0(sK7),k2_xboole_0(u1_struct_0(sK7),k2_struct_0(sK6)))),
% 5.51/1.10    inference(forward_demodulation,[],[f5096,f283])).
% 5.51/1.10  fof(f283,plain,(
% 5.51/1.10    u1_struct_0(sK6) = k2_struct_0(sK6)),
% 5.51/1.10    inference(resolution,[],[f259,f78])).
% 5.51/1.10  fof(f259,plain,(
% 5.51/1.10    l1_struct_0(sK6)),
% 5.51/1.10    inference(resolution,[],[f212,f81])).
% 5.51/1.10  fof(f212,plain,(
% 5.51/1.10    l1_pre_topc(sK6)),
% 5.51/1.10    inference(subsumption_resolution,[],[f196,f68])).
% 5.51/1.10  fof(f196,plain,(
% 5.51/1.10    l1_pre_topc(sK6) | ~l1_pre_topc(sK5)),
% 5.51/1.10    inference(resolution,[],[f70,f97])).
% 5.51/1.10  fof(f70,plain,(
% 5.51/1.10    m1_pre_topc(sK6,sK5)),
% 5.51/1.10    inference(cnf_transformation,[],[f47])).
% 5.51/1.10  fof(f5096,plain,(
% 5.51/1.10    r1_tarski(k2_struct_0(sK7),k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)))),
% 5.51/1.10    inference(subsumption_resolution,[],[f5095,f66])).
% 5.51/1.10  fof(f66,plain,(
% 5.51/1.10    ~v2_struct_0(sK5)),
% 5.51/1.10    inference(cnf_transformation,[],[f47])).
% 5.51/1.10  fof(f5095,plain,(
% 5.51/1.10    r1_tarski(k2_struct_0(sK7),k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))) | v2_struct_0(sK5)),
% 5.51/1.10    inference(subsumption_resolution,[],[f5094,f68])).
% 5.51/1.10  fof(f5094,plain,(
% 5.51/1.10    r1_tarski(k2_struct_0(sK7),k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))) | ~l1_pre_topc(sK5) | v2_struct_0(sK5)),
% 5.51/1.10    inference(subsumption_resolution,[],[f5093,f71])).
% 5.51/1.10  fof(f71,plain,(
% 5.51/1.10    ~v2_struct_0(sK7)),
% 5.51/1.10    inference(cnf_transformation,[],[f47])).
% 5.51/1.10  fof(f5093,plain,(
% 5.51/1.10    r1_tarski(k2_struct_0(sK7),k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))) | v2_struct_0(sK7) | ~l1_pre_topc(sK5) | v2_struct_0(sK5)),
% 5.51/1.10    inference(subsumption_resolution,[],[f5092,f72])).
% 5.51/1.10  fof(f5092,plain,(
% 5.51/1.10    r1_tarski(k2_struct_0(sK7),k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))) | ~m1_pre_topc(sK7,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(sK5) | v2_struct_0(sK5)),
% 5.51/1.10    inference(subsumption_resolution,[],[f5091,f69])).
% 5.51/1.10  fof(f69,plain,(
% 5.51/1.10    ~v2_struct_0(sK6)),
% 5.51/1.10    inference(cnf_transformation,[],[f47])).
% 5.51/1.10  fof(f5091,plain,(
% 5.51/1.10    r1_tarski(k2_struct_0(sK7),k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))) | v2_struct_0(sK6) | ~m1_pre_topc(sK7,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(sK5) | v2_struct_0(sK5)),
% 5.51/1.10    inference(subsumption_resolution,[],[f5090,f70])).
% 5.51/1.10  fof(f5090,plain,(
% 5.51/1.10    r1_tarski(k2_struct_0(sK7),k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))) | ~m1_pre_topc(sK6,sK5) | v2_struct_0(sK6) | ~m1_pre_topc(sK7,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(sK5) | v2_struct_0(sK5)),
% 5.51/1.10    inference(subsumption_resolution,[],[f5089,f718])).
% 5.51/1.10  fof(f718,plain,(
% 5.51/1.10    ~v2_struct_0(k1_tsep_1(sK5,sK7,sK6))),
% 5.51/1.10    inference(resolution,[],[f713,f111])).
% 5.51/1.10  fof(f111,plain,(
% 5.51/1.10    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X2,X1)) | ~sP4(X0,X1,X2)) )),
% 5.51/1.10    inference(cnf_transformation,[],[f65])).
% 5.51/1.10  fof(f65,plain,(
% 5.51/1.10    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X2,X1),X0) & v1_pre_topc(k1_tsep_1(X0,X2,X1)) & ~v2_struct_0(k1_tsep_1(X0,X2,X1))) | ~sP4(X0,X1,X2))),
% 5.51/1.10    inference(rectify,[],[f64])).
% 5.51/1.10  fof(f64,plain,(
% 5.51/1.10    ! [X0,X2,X1] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP4(X0,X2,X1))),
% 5.51/1.10    inference(nnf_transformation,[],[f41])).
% 5.51/1.10  fof(f41,plain,(
% 5.51/1.10    ! [X0,X2,X1] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP4(X0,X2,X1))),
% 5.51/1.10    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 5.51/1.10  fof(f713,plain,(
% 5.51/1.10    sP4(sK5,sK6,sK7)),
% 5.51/1.10    inference(subsumption_resolution,[],[f711,f72])).
% 5.51/1.10  fof(f711,plain,(
% 5.51/1.10    ~m1_pre_topc(sK7,sK5) | sP4(sK5,sK6,sK7)),
% 5.51/1.10    inference(resolution,[],[f245,f71])).
% 5.51/1.10  fof(f245,plain,(
% 5.51/1.10    ( ! [X14] : (v2_struct_0(X14) | ~m1_pre_topc(X14,sK5) | sP4(sK5,sK6,X14)) )),
% 5.51/1.10    inference(subsumption_resolution,[],[f244,f66])).
% 5.51/1.10  fof(f244,plain,(
% 5.51/1.10    ( ! [X14] : (sP4(sK5,sK6,X14) | ~m1_pre_topc(X14,sK5) | v2_struct_0(X14) | v2_struct_0(sK5)) )),
% 5.51/1.10    inference(subsumption_resolution,[],[f243,f68])).
% 5.51/1.10  fof(f243,plain,(
% 5.51/1.10    ( ! [X14] : (sP4(sK5,sK6,X14) | ~m1_pre_topc(X14,sK5) | v2_struct_0(X14) | ~l1_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 5.51/1.10    inference(subsumption_resolution,[],[f209,f69])).
% 5.51/1.10  fof(f209,plain,(
% 5.51/1.10    ( ! [X14] : (sP4(sK5,sK6,X14) | v2_struct_0(sK6) | ~m1_pre_topc(X14,sK5) | v2_struct_0(X14) | ~l1_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 5.51/1.10    inference(resolution,[],[f70,f114])).
% 5.51/1.10  fof(f114,plain,(
% 5.51/1.10    ( ! [X2,X0,X1] : (sP4(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 5.51/1.10    inference(cnf_transformation,[],[f42])).
% 5.51/1.10  fof(f42,plain,(
% 5.51/1.10    ! [X0,X1,X2] : (sP4(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 5.51/1.10    inference(definition_folding,[],[f35,f41])).
% 5.51/1.10  fof(f35,plain,(
% 5.51/1.10    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 5.51/1.10    inference(flattening,[],[f34])).
% 5.51/1.10  fof(f34,plain,(
% 5.51/1.10    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 5.51/1.10    inference(ennf_transformation,[],[f10])).
% 5.51/1.10  fof(f10,axiom,(
% 5.51/1.10    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 5.51/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 5.51/1.10  fof(f5089,plain,(
% 5.51/1.10    r1_tarski(k2_struct_0(sK7),k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))) | v2_struct_0(k1_tsep_1(sK5,sK7,sK6)) | ~m1_pre_topc(sK6,sK5) | v2_struct_0(sK6) | ~m1_pre_topc(sK7,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(sK5) | v2_struct_0(sK5)),
% 5.51/1.10    inference(subsumption_resolution,[],[f5088,f719])).
% 5.51/1.10  fof(f719,plain,(
% 5.51/1.10    v1_pre_topc(k1_tsep_1(sK5,sK7,sK6))),
% 5.51/1.10    inference(resolution,[],[f713,f112])).
% 5.51/1.10  fof(f112,plain,(
% 5.51/1.10    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X2,X1)) | ~sP4(X0,X1,X2)) )),
% 5.51/1.10    inference(cnf_transformation,[],[f65])).
% 5.51/1.10  fof(f5088,plain,(
% 5.51/1.10    r1_tarski(k2_struct_0(sK7),k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))) | ~v1_pre_topc(k1_tsep_1(sK5,sK7,sK6)) | v2_struct_0(k1_tsep_1(sK5,sK7,sK6)) | ~m1_pre_topc(sK6,sK5) | v2_struct_0(sK6) | ~m1_pre_topc(sK7,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(sK5) | v2_struct_0(sK5)),
% 5.51/1.10    inference(subsumption_resolution,[],[f5078,f720])).
% 5.51/1.10  fof(f720,plain,(
% 5.51/1.10    m1_pre_topc(k1_tsep_1(sK5,sK7,sK6),sK5)),
% 5.51/1.10    inference(resolution,[],[f713,f113])).
% 5.51/1.10  fof(f113,plain,(
% 5.51/1.10    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X2,X1),X0) | ~sP4(X0,X1,X2)) )),
% 5.51/1.10    inference(cnf_transformation,[],[f65])).
% 5.51/1.10  fof(f5078,plain,(
% 5.51/1.10    r1_tarski(k2_struct_0(sK7),k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))) | ~m1_pre_topc(k1_tsep_1(sK5,sK7,sK6),sK5) | ~v1_pre_topc(k1_tsep_1(sK5,sK7,sK6)) | v2_struct_0(k1_tsep_1(sK5,sK7,sK6)) | ~m1_pre_topc(sK6,sK5) | v2_struct_0(sK6) | ~m1_pre_topc(sK7,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(sK5) | v2_struct_0(sK5)),
% 5.51/1.10    inference(superposition,[],[f3609,f116])).
% 5.51/1.10  fof(f116,plain,(
% 5.51/1.10    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 5.51/1.10    inference(equality_resolution,[],[f99])).
% 5.51/1.10  fof(f99,plain,(
% 5.51/1.10    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 5.51/1.10    inference(cnf_transformation,[],[f60])).
% 5.51/1.10  fof(f60,plain,(
% 5.51/1.10    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 5.51/1.10    inference(nnf_transformation,[],[f26])).
% 5.51/1.10  fof(f26,plain,(
% 5.51/1.10    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 5.51/1.10    inference(flattening,[],[f25])).
% 5.51/1.10  fof(f25,plain,(
% 5.51/1.10    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 5.51/1.10    inference(ennf_transformation,[],[f8])).
% 5.51/1.10  fof(f8,axiom,(
% 5.51/1.10    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 5.51/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).
% 5.51/1.10  fof(f3609,plain,(
% 5.51/1.10    r1_tarski(k2_struct_0(sK7),u1_struct_0(k1_tsep_1(sK5,sK7,sK6)))),
% 5.51/1.10    inference(subsumption_resolution,[],[f3601,f720])).
% 5.51/1.10  fof(f3601,plain,(
% 5.51/1.10    r1_tarski(k2_struct_0(sK7),u1_struct_0(k1_tsep_1(sK5,sK7,sK6))) | ~m1_pre_topc(k1_tsep_1(sK5,sK7,sK6),sK5)),
% 5.51/1.10    inference(resolution,[],[f1938,f1084])).
% 5.51/1.10  fof(f1084,plain,(
% 5.51/1.10    m1_pre_topc(sK7,k1_tsep_1(sK5,sK7,sK6))),
% 5.51/1.10    inference(subsumption_resolution,[],[f1081,f72])).
% 5.51/1.10  fof(f1081,plain,(
% 5.51/1.10    ~m1_pre_topc(sK7,sK5) | m1_pre_topc(sK7,k1_tsep_1(sK5,sK7,sK6))),
% 5.51/1.10    inference(resolution,[],[f220,f71])).
% 5.51/1.10  fof(f220,plain,(
% 5.51/1.10    ( ! [X1] : (v2_struct_0(X1) | ~m1_pre_topc(X1,sK5) | m1_pre_topc(X1,k1_tsep_1(sK5,X1,sK6))) )),
% 5.51/1.10    inference(subsumption_resolution,[],[f219,f66])).
% 5.51/1.10  fof(f219,plain,(
% 5.51/1.10    ( ! [X1] : (m1_pre_topc(X1,k1_tsep_1(sK5,X1,sK6)) | ~m1_pre_topc(X1,sK5) | v2_struct_0(X1) | v2_struct_0(sK5)) )),
% 5.51/1.10    inference(subsumption_resolution,[],[f218,f67])).
% 5.51/1.10  fof(f67,plain,(
% 5.51/1.10    v2_pre_topc(sK5)),
% 5.51/1.10    inference(cnf_transformation,[],[f47])).
% 5.51/1.10  fof(f218,plain,(
% 5.51/1.10    ( ! [X1] : (m1_pre_topc(X1,k1_tsep_1(sK5,X1,sK6)) | ~m1_pre_topc(X1,sK5) | v2_struct_0(X1) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 5.51/1.10    inference(subsumption_resolution,[],[f217,f68])).
% 5.51/1.10  fof(f217,plain,(
% 5.51/1.10    ( ! [X1] : (m1_pre_topc(X1,k1_tsep_1(sK5,X1,sK6)) | ~m1_pre_topc(X1,sK5) | v2_struct_0(X1) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 5.51/1.10    inference(subsumption_resolution,[],[f198,f69])).
% 5.51/1.10  fof(f198,plain,(
% 5.51/1.10    ( ! [X1] : (m1_pre_topc(X1,k1_tsep_1(sK5,X1,sK6)) | v2_struct_0(sK6) | ~m1_pre_topc(X1,sK5) | v2_struct_0(X1) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 5.51/1.10    inference(resolution,[],[f70,f98])).
% 5.51/1.10  fof(f98,plain,(
% 5.51/1.10    ( ! [X2,X0,X1] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 5.51/1.10    inference(cnf_transformation,[],[f24])).
% 5.51/1.10  fof(f24,plain,(
% 5.51/1.10    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 5.51/1.10    inference(flattening,[],[f23])).
% 5.51/1.10  fof(f23,plain,(
% 5.51/1.10    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 5.51/1.10    inference(ennf_transformation,[],[f12])).
% 5.51/1.10  fof(f12,axiom,(
% 5.51/1.10    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)))))),
% 5.51/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tsep_1)).
% 5.51/1.10  fof(f1938,plain,(
% 5.51/1.10    ( ! [X10] : (~m1_pre_topc(sK7,X10) | r1_tarski(k2_struct_0(sK7),u1_struct_0(X10)) | ~m1_pre_topc(X10,sK5)) )),
% 5.51/1.10    inference(forward_demodulation,[],[f332,f371])).
% 5.51/1.10  fof(f332,plain,(
% 5.51/1.10    ( ! [X10] : (r1_tarski(u1_struct_0(sK7),u1_struct_0(X10)) | ~m1_pre_topc(sK7,X10) | ~m1_pre_topc(X10,sK5)) )),
% 5.51/1.10    inference(subsumption_resolution,[],[f331,f67])).
% 5.51/1.10  fof(f331,plain,(
% 5.51/1.10    ( ! [X10] : (r1_tarski(u1_struct_0(sK7),u1_struct_0(X10)) | ~m1_pre_topc(sK7,X10) | ~m1_pre_topc(X10,sK5) | ~v2_pre_topc(sK5)) )),
% 5.51/1.10    inference(subsumption_resolution,[],[f300,f68])).
% 5.51/1.10  fof(f300,plain,(
% 5.51/1.10    ( ! [X10] : (r1_tarski(u1_struct_0(sK7),u1_struct_0(X10)) | ~m1_pre_topc(sK7,X10) | ~m1_pre_topc(X10,sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5)) )),
% 5.51/1.10    inference(resolution,[],[f72,f103])).
% 5.51/1.10  fof(f103,plain,(
% 5.51/1.10    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 5.51/1.10    inference(cnf_transformation,[],[f61])).
% 5.51/1.10  fof(f61,plain,(
% 5.51/1.10    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 5.51/1.10    inference(nnf_transformation,[],[f30])).
% 5.51/1.10  fof(f30,plain,(
% 5.51/1.10    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 5.51/1.10    inference(flattening,[],[f29])).
% 5.51/1.10  fof(f29,plain,(
% 5.51/1.10    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 5.51/1.10    inference(ennf_transformation,[],[f13])).
% 5.51/1.10  fof(f13,axiom,(
% 5.51/1.10    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 5.51/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 5.51/1.10  fof(f6408,plain,(
% 5.51/1.10    k2_struct_0(sK7) = k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6)) | ~r1_tarski(k2_struct_0(sK7),k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6)))),
% 5.51/1.10    inference(resolution,[],[f6370,f107])).
% 5.51/1.10  fof(f107,plain,(
% 5.51/1.10    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 5.51/1.10    inference(cnf_transformation,[],[f63])).
% 5.51/1.10  fof(f63,plain,(
% 5.51/1.10    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 5.51/1.10    inference(flattening,[],[f62])).
% 5.51/1.10  fof(f62,plain,(
% 5.51/1.10    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 5.51/1.10    inference(nnf_transformation,[],[f1])).
% 5.51/1.10  fof(f1,axiom,(
% 5.51/1.10    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 5.51/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 5.51/1.10  fof(f6370,plain,(
% 5.51/1.10    r1_tarski(k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6)),k2_struct_0(sK7))),
% 5.51/1.10    inference(forward_demodulation,[],[f6369,f371])).
% 5.51/1.10  fof(f6369,plain,(
% 5.51/1.10    r1_tarski(k2_xboole_0(u1_struct_0(sK7),k2_struct_0(sK6)),k2_struct_0(sK7))),
% 5.51/1.10    inference(forward_demodulation,[],[f6368,f283])).
% 5.51/1.10  fof(f6368,plain,(
% 5.51/1.10    r1_tarski(k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)),k2_struct_0(sK7))),
% 5.51/1.10    inference(subsumption_resolution,[],[f6367,f307])).
% 5.51/1.10  fof(f6367,plain,(
% 5.51/1.10    r1_tarski(k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)),k2_struct_0(sK7)) | ~l1_pre_topc(sK7)),
% 5.51/1.10    inference(subsumption_resolution,[],[f6366,f71])).
% 5.51/1.10  fof(f6366,plain,(
% 5.51/1.10    r1_tarski(k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)),k2_struct_0(sK7)) | v2_struct_0(sK7) | ~l1_pre_topc(sK7)),
% 5.51/1.10    inference(subsumption_resolution,[],[f6365,f3461])).
% 5.51/1.10  fof(f3461,plain,(
% 5.51/1.10    m1_pre_topc(sK7,sK7)),
% 5.51/1.10    inference(subsumption_resolution,[],[f3460,f72])).
% 5.51/1.10  fof(f3460,plain,(
% 5.51/1.10    m1_pre_topc(sK7,sK7) | ~m1_pre_topc(sK7,sK5)),
% 5.51/1.10    inference(subsumption_resolution,[],[f3457,f118])).
% 5.51/1.10  fof(f118,plain,(
% 5.51/1.10    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 5.51/1.10    inference(equality_resolution,[],[f105])).
% 5.51/1.10  fof(f105,plain,(
% 5.51/1.10    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 5.51/1.10    inference(cnf_transformation,[],[f63])).
% 5.51/1.10  fof(f3457,plain,(
% 5.51/1.10    ~r1_tarski(k2_struct_0(sK7),k2_struct_0(sK7)) | m1_pre_topc(sK7,sK7) | ~m1_pre_topc(sK7,sK5)),
% 5.51/1.10    inference(superposition,[],[f1670,f371])).
% 5.51/1.10  fof(f1670,plain,(
% 5.51/1.10    ( ! [X8] : (~r1_tarski(k2_struct_0(sK7),u1_struct_0(X8)) | m1_pre_topc(sK7,X8) | ~m1_pre_topc(X8,sK5)) )),
% 5.51/1.10    inference(forward_demodulation,[],[f328,f371])).
% 5.51/1.10  fof(f328,plain,(
% 5.51/1.10    ( ! [X8] : (m1_pre_topc(sK7,X8) | ~r1_tarski(u1_struct_0(sK7),u1_struct_0(X8)) | ~m1_pre_topc(X8,sK5)) )),
% 5.51/1.10    inference(subsumption_resolution,[],[f327,f67])).
% 5.51/1.10  fof(f327,plain,(
% 5.51/1.10    ( ! [X8] : (m1_pre_topc(sK7,X8) | ~r1_tarski(u1_struct_0(sK7),u1_struct_0(X8)) | ~m1_pre_topc(X8,sK5) | ~v2_pre_topc(sK5)) )),
% 5.51/1.10    inference(subsumption_resolution,[],[f298,f68])).
% 5.51/1.10  fof(f298,plain,(
% 5.51/1.10    ( ! [X8] : (m1_pre_topc(sK7,X8) | ~r1_tarski(u1_struct_0(sK7),u1_struct_0(X8)) | ~m1_pre_topc(X8,sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5)) )),
% 5.51/1.10    inference(resolution,[],[f72,f102])).
% 5.51/1.10  fof(f102,plain,(
% 5.51/1.10    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 5.51/1.10    inference(cnf_transformation,[],[f61])).
% 5.51/1.10  fof(f6365,plain,(
% 5.51/1.10    r1_tarski(k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)),k2_struct_0(sK7)) | ~m1_pre_topc(sK7,sK7) | v2_struct_0(sK7) | ~l1_pre_topc(sK7)),
% 5.51/1.10    inference(subsumption_resolution,[],[f6364,f69])).
% 5.51/1.10  fof(f6364,plain,(
% 5.51/1.10    r1_tarski(k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)),k2_struct_0(sK7)) | v2_struct_0(sK6) | ~m1_pre_topc(sK7,sK7) | v2_struct_0(sK7) | ~l1_pre_topc(sK7)),
% 5.51/1.10    inference(subsumption_resolution,[],[f6363,f75])).
% 5.51/1.10  fof(f75,plain,(
% 5.51/1.10    m1_pre_topc(sK6,sK7)),
% 5.51/1.10    inference(cnf_transformation,[],[f47])).
% 5.51/1.10  fof(f6363,plain,(
% 5.51/1.10    r1_tarski(k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)),k2_struct_0(sK7)) | ~m1_pre_topc(sK6,sK7) | v2_struct_0(sK6) | ~m1_pre_topc(sK7,sK7) | v2_struct_0(sK7) | ~l1_pre_topc(sK7)),
% 5.51/1.10    inference(subsumption_resolution,[],[f6362,f4508])).
% 5.51/1.10  fof(f4508,plain,(
% 5.51/1.10    ~v2_struct_0(k1_tsep_1(sK7,sK7,sK6))),
% 5.51/1.10    inference(resolution,[],[f4507,f111])).
% 5.51/1.10  fof(f4507,plain,(
% 5.51/1.10    sP4(sK7,sK6,sK7)),
% 5.51/1.10    inference(subsumption_resolution,[],[f895,f3461])).
% 5.51/1.10  fof(f895,plain,(
% 5.51/1.10    ~m1_pre_topc(sK7,sK7) | sP4(sK7,sK6,sK7)),
% 5.51/1.10    inference(resolution,[],[f482,f71])).
% 5.51/1.10  fof(f482,plain,(
% 5.51/1.10    ( ! [X14] : (v2_struct_0(X14) | ~m1_pre_topc(X14,sK7) | sP4(sK7,sK6,X14)) )),
% 5.51/1.10    inference(subsumption_resolution,[],[f481,f71])).
% 5.51/1.10  fof(f481,plain,(
% 5.51/1.10    ( ! [X14] : (sP4(sK7,sK6,X14) | ~m1_pre_topc(X14,sK7) | v2_struct_0(X14) | v2_struct_0(sK7)) )),
% 5.51/1.10    inference(subsumption_resolution,[],[f480,f307])).
% 5.51/1.10  fof(f480,plain,(
% 5.51/1.10    ( ! [X14] : (sP4(sK7,sK6,X14) | ~m1_pre_topc(X14,sK7) | v2_struct_0(X14) | ~l1_pre_topc(sK7) | v2_struct_0(sK7)) )),
% 5.51/1.10    inference(subsumption_resolution,[],[f449,f69])).
% 5.51/1.10  fof(f449,plain,(
% 5.51/1.10    ( ! [X14] : (sP4(sK7,sK6,X14) | v2_struct_0(sK6) | ~m1_pre_topc(X14,sK7) | v2_struct_0(X14) | ~l1_pre_topc(sK7) | v2_struct_0(sK7)) )),
% 5.51/1.10    inference(resolution,[],[f75,f114])).
% 5.51/1.10  fof(f6362,plain,(
% 5.51/1.10    r1_tarski(k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)),k2_struct_0(sK7)) | v2_struct_0(k1_tsep_1(sK7,sK7,sK6)) | ~m1_pre_topc(sK6,sK7) | v2_struct_0(sK6) | ~m1_pre_topc(sK7,sK7) | v2_struct_0(sK7) | ~l1_pre_topc(sK7)),
% 5.51/1.10    inference(subsumption_resolution,[],[f6361,f4509])).
% 5.51/1.10  fof(f4509,plain,(
% 5.51/1.10    v1_pre_topc(k1_tsep_1(sK7,sK7,sK6))),
% 5.51/1.10    inference(resolution,[],[f4507,f112])).
% 5.51/1.10  fof(f6361,plain,(
% 5.51/1.10    r1_tarski(k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)),k2_struct_0(sK7)) | ~v1_pre_topc(k1_tsep_1(sK7,sK7,sK6)) | v2_struct_0(k1_tsep_1(sK7,sK7,sK6)) | ~m1_pre_topc(sK6,sK7) | v2_struct_0(sK6) | ~m1_pre_topc(sK7,sK7) | v2_struct_0(sK7) | ~l1_pre_topc(sK7)),
% 5.51/1.10    inference(subsumption_resolution,[],[f6359,f4510])).
% 5.51/1.10  fof(f4510,plain,(
% 5.51/1.10    m1_pre_topc(k1_tsep_1(sK7,sK7,sK6),sK7)),
% 5.51/1.10    inference(resolution,[],[f4507,f113])).
% 5.51/1.10  fof(f6359,plain,(
% 5.51/1.10    r1_tarski(k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)),k2_struct_0(sK7)) | ~m1_pre_topc(k1_tsep_1(sK7,sK7,sK6),sK7) | ~v1_pre_topc(k1_tsep_1(sK7,sK7,sK6)) | v2_struct_0(k1_tsep_1(sK7,sK7,sK6)) | ~m1_pre_topc(sK6,sK7) | v2_struct_0(sK6) | ~m1_pre_topc(sK7,sK7) | v2_struct_0(sK7) | ~l1_pre_topc(sK7)),
% 5.51/1.10    inference(duplicate_literal_removal,[],[f6357])).
% 5.51/1.10  fof(f6357,plain,(
% 5.51/1.10    r1_tarski(k2_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)),k2_struct_0(sK7)) | ~m1_pre_topc(k1_tsep_1(sK7,sK7,sK6),sK7) | ~v1_pre_topc(k1_tsep_1(sK7,sK7,sK6)) | v2_struct_0(k1_tsep_1(sK7,sK7,sK6)) | ~m1_pre_topc(sK6,sK7) | v2_struct_0(sK6) | ~m1_pre_topc(sK7,sK7) | v2_struct_0(sK7) | ~l1_pre_topc(sK7) | v2_struct_0(sK7)),
% 5.51/1.10    inference(superposition,[],[f6096,f116])).
% 5.51/1.10  fof(f6096,plain,(
% 5.51/1.10    r1_tarski(u1_struct_0(k1_tsep_1(sK7,sK7,sK6)),k2_struct_0(sK7))),
% 5.51/1.10    inference(resolution,[],[f3521,f4510])).
% 5.51/1.10  fof(f3521,plain,(
% 5.51/1.10    ( ! [X11] : (~m1_pre_topc(X11,sK7) | r1_tarski(u1_struct_0(X11),k2_struct_0(sK7))) )),
% 5.51/1.10    inference(forward_demodulation,[],[f3520,f371])).
% 5.51/1.10  fof(f3520,plain,(
% 5.51/1.10    ( ! [X11] : (r1_tarski(u1_struct_0(X11),u1_struct_0(sK7)) | ~m1_pre_topc(X11,sK7)) )),
% 5.51/1.10    inference(subsumption_resolution,[],[f3519,f326])).
% 5.51/1.10  fof(f326,plain,(
% 5.51/1.10    v2_pre_topc(sK7)),
% 5.51/1.10    inference(subsumption_resolution,[],[f325,f67])).
% 5.51/1.10  fof(f325,plain,(
% 5.51/1.10    v2_pre_topc(sK7) | ~v2_pre_topc(sK5)),
% 5.51/1.10    inference(subsumption_resolution,[],[f297,f68])).
% 5.51/1.10  fof(f297,plain,(
% 5.51/1.10    v2_pre_topc(sK7) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5)),
% 5.51/1.10    inference(resolution,[],[f72,f101])).
% 5.51/1.10  fof(f101,plain,(
% 5.51/1.10    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 5.51/1.10    inference(cnf_transformation,[],[f28])).
% 5.51/1.10  fof(f28,plain,(
% 5.51/1.10    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 5.51/1.10    inference(flattening,[],[f27])).
% 5.51/1.10  fof(f27,plain,(
% 5.51/1.10    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 5.51/1.10    inference(ennf_transformation,[],[f3])).
% 5.51/1.10  fof(f3,axiom,(
% 5.51/1.10    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 5.51/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 5.51/1.10  fof(f3519,plain,(
% 5.51/1.10    ( ! [X11] : (r1_tarski(u1_struct_0(X11),u1_struct_0(sK7)) | ~m1_pre_topc(X11,sK7) | ~v2_pre_topc(sK7)) )),
% 5.51/1.10    inference(subsumption_resolution,[],[f3489,f307])).
% 5.51/1.10  fof(f3489,plain,(
% 5.51/1.10    ( ! [X11] : (r1_tarski(u1_struct_0(X11),u1_struct_0(sK7)) | ~m1_pre_topc(X11,sK7) | ~l1_pre_topc(sK7) | ~v2_pre_topc(sK7)) )),
% 5.51/1.10    inference(duplicate_literal_removal,[],[f3478])).
% 5.51/1.10  fof(f3478,plain,(
% 5.51/1.10    ( ! [X11] : (r1_tarski(u1_struct_0(X11),u1_struct_0(sK7)) | ~m1_pre_topc(X11,sK7) | ~m1_pre_topc(X11,sK7) | ~l1_pre_topc(sK7) | ~v2_pre_topc(sK7)) )),
% 5.51/1.10    inference(resolution,[],[f3461,f103])).
% 5.51/1.10  fof(f1391,plain,(
% 5.51/1.10    ( ! [X1] : (~r1_xboole_0(k2_struct_0(sK8),k2_xboole_0(X1,k2_struct_0(sK6)))) )),
% 5.51/1.10    inference(resolution,[],[f883,f110])).
% 5.51/1.10  fof(f110,plain,(
% 5.51/1.10    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 5.51/1.10    inference(cnf_transformation,[],[f33])).
% 5.51/1.10  fof(f33,plain,(
% 5.51/1.10    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 5.51/1.10    inference(ennf_transformation,[],[f2])).
% 5.51/1.10  fof(f2,axiom,(
% 5.51/1.10    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 5.51/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 5.51/1.10  fof(f883,plain,(
% 5.51/1.10    ~r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6))),
% 5.51/1.10    inference(forward_demodulation,[],[f882,f513])).
% 5.51/1.10  fof(f882,plain,(
% 5.51/1.10    ~r1_xboole_0(u1_struct_0(sK8),k2_struct_0(sK6))),
% 5.51/1.10    inference(forward_demodulation,[],[f563,f283])).
% 5.51/1.10  fof(f563,plain,(
% 5.51/1.10    ~r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK6))),
% 5.51/1.10    inference(subsumption_resolution,[],[f562,f489])).
% 5.51/1.10  fof(f562,plain,(
% 5.51/1.10    ~r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK6)) | ~l1_struct_0(sK8)),
% 5.51/1.10    inference(subsumption_resolution,[],[f561,f259])).
% 5.51/1.10  fof(f561,plain,(
% 5.51/1.10    ~r1_xboole_0(u1_struct_0(sK8),u1_struct_0(sK6)) | ~l1_struct_0(sK6) | ~l1_struct_0(sK8)),
% 5.51/1.10    inference(resolution,[],[f557,f80])).
% 5.51/1.10  fof(f80,plain,(
% 5.51/1.10    ( ! [X0,X1] : (r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 5.51/1.10    inference(cnf_transformation,[],[f48])).
% 5.51/1.10  fof(f557,plain,(
% 5.51/1.10    ~r1_tsep_1(sK8,sK6)),
% 5.51/1.10    inference(subsumption_resolution,[],[f556,f489])).
% 5.51/1.10  fof(f556,plain,(
% 5.51/1.10    ~r1_tsep_1(sK8,sK6) | ~l1_struct_0(sK8)),
% 5.51/1.10    inference(subsumption_resolution,[],[f554,f259])).
% 5.51/1.10  fof(f554,plain,(
% 5.51/1.10    ~r1_tsep_1(sK8,sK6) | ~l1_struct_0(sK6) | ~l1_struct_0(sK8)),
% 5.51/1.10    inference(resolution,[],[f551,f104])).
% 5.51/1.10  fof(f551,plain,(
% 5.51/1.10    ~r1_tsep_1(sK6,sK8)),
% 5.51/1.10    inference(subsumption_resolution,[],[f550,f259])).
% 5.51/1.10  fof(f550,plain,(
% 5.51/1.10    ~r1_tsep_1(sK6,sK8) | ~l1_struct_0(sK6)),
% 5.51/1.10    inference(subsumption_resolution,[],[f549,f489])).
% 5.51/1.10  fof(f549,plain,(
% 5.51/1.10    ~r1_tsep_1(sK6,sK8) | ~l1_struct_0(sK8) | ~l1_struct_0(sK6)),
% 5.51/1.10    inference(duplicate_literal_removal,[],[f547])).
% 5.51/1.10  fof(f547,plain,(
% 5.51/1.10    ~r1_tsep_1(sK6,sK8) | ~r1_tsep_1(sK6,sK8) | ~l1_struct_0(sK8) | ~l1_struct_0(sK6)),
% 5.51/1.10    inference(resolution,[],[f77,f104])).
% 5.51/1.10  fof(f77,plain,(
% 5.51/1.10    ~r1_tsep_1(sK8,sK6) | ~r1_tsep_1(sK6,sK8)),
% 5.51/1.10    inference(cnf_transformation,[],[f47])).
% 5.51/1.10  % SZS output end Proof for theBenchmark
% 5.51/1.10  % (21655)------------------------------
% 5.51/1.10  % (21655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.51/1.10  % (21655)Termination reason: Refutation
% 5.51/1.10  
% 5.51/1.10  % (21655)Memory used [KB]: 4093
% 5.51/1.10  % (21655)Time elapsed: 0.637 s
% 5.51/1.10  % (21655)------------------------------
% 5.51/1.10  % (21655)------------------------------
% 5.51/1.12  % (21640)Success in time 0.762 s
%------------------------------------------------------------------------------
