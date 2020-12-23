%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  109 (1388 expanded)
%              Number of leaves         :   15 ( 619 expanded)
%              Depth                    :   23
%              Number of atoms          :  578 (15490 expanded)
%              Number of equality atoms :   72 ( 109 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1350,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1349,f1283])).

fof(f1283,plain,(
    ~ r1_tarski(k2_struct_0(k1_tsep_1(sK0,sK1,sK3)),k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f664,f1279])).

fof(f1279,plain,(
    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f1047,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f1047,plain,(
    l1_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f601,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f601,plain,(
    l1_pre_topc(k1_tsep_1(sK0,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f38,f140,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f140,plain,(
    m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) ),
    inference(unit_resulting_resolution,[],[f36,f38,f39,f40,f43,f44,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f44,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    & m1_pre_topc(sK3,sK2)
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f25,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
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
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2)
                & m1_pre_topc(X3,X2)
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),X2)
              & m1_pre_topc(X3,X2)
              & m1_pre_topc(sK1,X2)
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),X2)
            & m1_pre_topc(X3,X2)
            & m1_pre_topc(sK1,X2)
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK2)
          & m1_pre_topc(X3,sK2)
          & m1_pre_topc(sK1,sK2)
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK2)
        & m1_pre_topc(X3,sK2)
        & m1_pre_topc(sK1,sK2)
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
      & m1_pre_topc(sK3,sK2)
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tmap_1)).

fof(f43,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f664,plain,(
    ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f602,f120])).

fof(f120,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unit_resulting_resolution,[],[f113,f48])).

fof(f113,plain,(
    l1_struct_0(sK2) ),
    inference(unit_resulting_resolution,[],[f100,f49])).

fof(f100,plain,(
    l1_pre_topc(sK2) ),
    inference(unit_resulting_resolution,[],[f38,f42,f60])).

fof(f42,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f602,plain,(
    ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f37,f38,f42,f47,f140,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f19])).

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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f47,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f1349,plain,(
    r1_tarski(k2_struct_0(k1_tsep_1(sK0,sK1,sK3)),k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f1316,f1347])).

fof(f1347,plain,(
    k2_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_struct_0(k1_tsep_1(sK2,sK1,sK3)) ),
    inference(forward_demodulation,[],[f1345,f1282])).

fof(f1282,plain,(
    k2_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) ),
    inference(backward_demodulation,[],[f690,f1279])).

fof(f690,plain,(
    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) ),
    inference(forward_demodulation,[],[f689,f260])).

fof(f260,plain,(
    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f259,f96])).

fof(f96,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unit_resulting_resolution,[],[f89,f48])).

fof(f89,plain,(
    l1_struct_0(sK1) ),
    inference(unit_resulting_resolution,[],[f82,f49])).

fof(f82,plain,(
    l1_pre_topc(sK1) ),
    inference(unit_resulting_resolution,[],[f38,f40,f60])).

fof(f259,plain,(
    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),k2_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f258,f150])).

fof(f150,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unit_resulting_resolution,[],[f143,f48])).

fof(f143,plain,(
    l1_struct_0(sK3) ),
    inference(unit_resulting_resolution,[],[f124,f49])).

fof(f124,plain,(
    l1_pre_topc(sK3) ),
    inference(unit_resulting_resolution,[],[f38,f44,f60])).

fof(f258,plain,(
    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f257,f36])).

fof(f257,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f256,f38])).

fof(f256,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f255,f39])).

fof(f255,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f254,f40])).

fof(f254,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f253,f43])).

fof(f253,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f252,f44])).

fof(f252,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f251,f128])).

fof(f128,plain,(
    ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f36,f38,f39,f40,f43,f44,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f251,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f250,f140])).

fof(f250,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f134,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f134,plain,(
    v1_pre_topc(k1_tsep_1(sK0,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f36,f38,f39,f40,f43,f44,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f689,plain,(
    k2_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) ),
    inference(forward_demodulation,[],[f688,f96])).

fof(f688,plain,(
    k2_xboole_0(u1_struct_0(sK1),k2_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) ),
    inference(forward_demodulation,[],[f687,f150])).

fof(f687,plain,(
    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f686,f41])).

fof(f41,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f686,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f685,f100])).

fof(f685,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f684,f39])).

fof(f684,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f683,f45])).

fof(f45,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f683,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f682,f43])).

fof(f682,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f681,f46])).

fof(f46,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f681,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f680,f170])).

fof(f170,plain,(
    ~ v2_struct_0(k1_tsep_1(sK2,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f41,f100,f39,f45,f43,f46,f65])).

fof(f680,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | v2_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f679,f178])).

fof(f178,plain,(
    m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2) ),
    inference(unit_resulting_resolution,[],[f41,f100,f39,f45,f43,f46,f67])).

fof(f679,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
    | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | v2_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f174,f69])).

fof(f174,plain,(
    v1_pre_topc(k1_tsep_1(sK2,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f41,f100,f39,f45,f43,f46,f66])).

fof(f1345,plain,(
    u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) = k2_struct_0(k1_tsep_1(sK2,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f1315,f48])).

fof(f1315,plain,(
    l1_struct_0(k1_tsep_1(sK2,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f1176,f49])).

fof(f1176,plain,(
    l1_pre_topc(k1_tsep_1(sK2,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f100,f178,f60])).

fof(f1316,plain,(
    r1_tarski(k2_struct_0(k1_tsep_1(sK2,sK1,sK3)),k2_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f100,f178,f1176,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ( ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK4(X0,X1)
                      | ~ r2_hidden(X3,u1_pre_topc(X0))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) )
                & ( ( sK4(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1))
                    & r2_hidden(sK5(X0,X1),u1_pre_topc(X0))
                    & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
                  | r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) )
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X5] :
                    ( ( ( r2_hidden(X5,u1_pre_topc(X1))
                        | ! [X6] :
                            ( k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5
                            | ~ r2_hidden(X6,u1_pre_topc(X0))
                            | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ( k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X5),k2_struct_0(X1)) = X5
                          & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X0))
                          & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X5,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f29,f32,f31,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                | ~ r2_hidden(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X2,u1_pre_topc(X1)) )
          & ( ? [X4] :
                ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                & r2_hidden(X4,u1_pre_topc(X0))
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X2,u1_pre_topc(X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK4(X0,X1)
              | ~ r2_hidden(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK4(X0,X1)
              & r2_hidden(X4,u1_pre_topc(X0))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) )
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK4(X0,X1)
          & r2_hidden(X4,u1_pre_topc(X0))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK4(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1))
        & r2_hidden(sK5(X0,X1),u1_pre_topc(X0))
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5
          & r2_hidden(X7,u1_pre_topc(X0))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X5),k2_struct_0(X1)) = X5
        & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X0))
        & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X4] :
                        ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                        & r2_hidden(X4,u1_pre_topc(X0))
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X5] :
                    ( ( ( r2_hidden(X5,u1_pre_topc(X1))
                        | ! [X6] :
                            ( k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5
                            | ~ r2_hidden(X6,u1_pre_topc(X0))
                            | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X7] :
                            ( k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5
                            & r2_hidden(X7,u1_pre_topc(X0))
                            & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X5,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X2] :
                    ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                        | ! [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                            | ~ r2_hidden(X3,u1_pre_topc(X0))
                            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                            & r2_hidden(X3,u1_pre_topc(X0))
                            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X2] :
                    ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                        | ! [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                            | ~ r2_hidden(X3,u1_pre_topc(X0))
                            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                            & r2_hidden(X3,u1_pre_topc(X0))
                            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:43:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (13820)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (13826)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (13823)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (13824)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (13838)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.49  % (13828)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (13836)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  % (13821)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (13835)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.49  % (13822)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (13832)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (13829)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (13827)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.49  % (13821)Refutation not found, incomplete strategy% (13821)------------------------------
% 0.20/0.49  % (13821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (13821)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (13821)Memory used [KB]: 10618
% 0.20/0.49  % (13821)Time elapsed: 0.045 s
% 0.20/0.49  % (13821)------------------------------
% 0.20/0.49  % (13821)------------------------------
% 0.20/0.49  % (13833)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (13831)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.50  % (13825)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (13837)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.50  % (13839)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  % (13834)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.51  % (13830)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.51  % (13830)Refutation not found, incomplete strategy% (13830)------------------------------
% 0.20/0.51  % (13830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (13830)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (13830)Memory used [KB]: 6268
% 0.20/0.51  % (13830)Time elapsed: 0.098 s
% 0.20/0.51  % (13830)------------------------------
% 0.20/0.51  % (13830)------------------------------
% 0.20/0.52  % (13840)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.52  % (13840)Refutation not found, incomplete strategy% (13840)------------------------------
% 0.20/0.52  % (13840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (13840)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (13840)Memory used [KB]: 10618
% 0.20/0.52  % (13840)Time elapsed: 0.111 s
% 0.20/0.52  % (13840)------------------------------
% 0.20/0.52  % (13840)------------------------------
% 0.20/0.55  % (13835)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f1350,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(subsumption_resolution,[],[f1349,f1283])).
% 0.20/0.55  fof(f1283,plain,(
% 0.20/0.55    ~r1_tarski(k2_struct_0(k1_tsep_1(sK0,sK1,sK3)),k2_struct_0(sK2))),
% 0.20/0.55    inference(backward_demodulation,[],[f664,f1279])).
% 0.20/0.55  fof(f1279,plain,(
% 0.20/0.55    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_struct_0(k1_tsep_1(sK0,sK1,sK3))),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f1047,f48])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,plain,(
% 0.20/0.55    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.55  fof(f1047,plain,(
% 0.20/0.55    l1_struct_0(k1_tsep_1(sK0,sK1,sK3))),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f601,f49])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,plain,(
% 0.20/0.55    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.55  fof(f601,plain,(
% 0.20/0.55    l1_pre_topc(k1_tsep_1(sK0,sK1,sK3))),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f38,f140,f60])).
% 0.20/0.55  fof(f60,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.55  fof(f140,plain,(
% 0.20/0.55    m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f36,f38,f39,f40,f43,f44,f67])).
% 0.20/0.55  fof(f67,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | v2_struct_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.55    inference(flattening,[],[f20])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    m1_pre_topc(sK3,sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    (((~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f25,f24,f23,f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK2) & m1_pre_topc(X3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK2) & m1_pre_topc(X3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f11,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.55    inference(flattening,[],[f10])).
% 0.20/0.55  fof(f10,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & (m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,negated_conjecture,(
% 0.20/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 0.20/0.55    inference(negated_conjecture,[],[f8])).
% 0.20/0.55  fof(f8,conjecture,(
% 0.20/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tmap_1)).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    ~v2_struct_0(sK3)),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    m1_pre_topc(sK1,sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ~v2_struct_0(sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ~v2_struct_0(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    l1_pre_topc(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f664,plain,(
% 0.20/0.55    ~r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),k2_struct_0(sK2))),
% 0.20/0.55    inference(forward_demodulation,[],[f602,f120])).
% 0.20/0.55  fof(f120,plain,(
% 0.20/0.55    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f113,f48])).
% 0.20/0.55  fof(f113,plain,(
% 0.20/0.55    l1_struct_0(sK2)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f100,f49])).
% 0.20/0.55  fof(f100,plain,(
% 0.20/0.55    l1_pre_topc(sK2)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f38,f42,f60])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    m1_pre_topc(sK2,sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f602,plain,(
% 0.20/0.55    ~r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f37,f38,f42,f47,f140,f63])).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f35])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.55    inference(nnf_transformation,[],[f19])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.55    inference(flattening,[],[f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    v2_pre_topc(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f1349,plain,(
% 0.20/0.55    r1_tarski(k2_struct_0(k1_tsep_1(sK0,sK1,sK3)),k2_struct_0(sK2))),
% 0.20/0.55    inference(backward_demodulation,[],[f1316,f1347])).
% 0.20/0.55  fof(f1347,plain,(
% 0.20/0.55    k2_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_struct_0(k1_tsep_1(sK2,sK1,sK3))),
% 0.20/0.55    inference(forward_demodulation,[],[f1345,f1282])).
% 0.20/0.55  fof(f1282,plain,(
% 0.20/0.55    k2_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))),
% 0.20/0.55    inference(backward_demodulation,[],[f690,f1279])).
% 0.20/0.55  fof(f690,plain,(
% 0.20/0.55    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))),
% 0.20/0.55    inference(forward_demodulation,[],[f689,f260])).
% 0.20/0.55  fof(f260,plain,(
% 0.20/0.55    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3))),
% 0.20/0.55    inference(forward_demodulation,[],[f259,f96])).
% 0.20/0.55  fof(f96,plain,(
% 0.20/0.55    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f89,f48])).
% 0.20/0.55  fof(f89,plain,(
% 0.20/0.55    l1_struct_0(sK1)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f82,f49])).
% 0.20/0.55  fof(f82,plain,(
% 0.20/0.55    l1_pre_topc(sK1)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f38,f40,f60])).
% 0.20/0.55  fof(f259,plain,(
% 0.20/0.55    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),k2_struct_0(sK3))),
% 0.20/0.55    inference(forward_demodulation,[],[f258,f150])).
% 0.20/0.55  fof(f150,plain,(
% 0.20/0.55    u1_struct_0(sK3) = k2_struct_0(sK3)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f143,f48])).
% 0.20/0.55  fof(f143,plain,(
% 0.20/0.55    l1_struct_0(sK3)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f124,f49])).
% 0.20/0.55  fof(f124,plain,(
% 0.20/0.55    l1_pre_topc(sK3)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f38,f44,f60])).
% 0.20/0.55  fof(f258,plain,(
% 0.20/0.55    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))),
% 0.20/0.55    inference(subsumption_resolution,[],[f257,f36])).
% 0.20/0.55  fof(f257,plain,(
% 0.20/0.55    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | v2_struct_0(sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f256,f38])).
% 0.20/0.55  fof(f256,plain,(
% 0.20/0.55    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f255,f39])).
% 0.20/0.55  fof(f255,plain,(
% 0.20/0.55    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f254,f40])).
% 0.20/0.55  fof(f254,plain,(
% 0.20/0.55    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f253,f43])).
% 0.20/0.55  fof(f253,plain,(
% 0.20/0.55    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f252,f44])).
% 0.20/0.55  fof(f252,plain,(
% 0.20/0.55    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f251,f128])).
% 0.20/0.55  fof(f128,plain,(
% 0.20/0.55    ~v2_struct_0(k1_tsep_1(sK0,sK1,sK3))),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f36,f38,f39,f40,f43,f44,f65])).
% 0.20/0.55  fof(f65,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f251,plain,(
% 0.20/0.55    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f250,f140])).
% 0.20/0.55  fof(f250,plain,(
% 0.20/0.55    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.55    inference(resolution,[],[f134,f69])).
% 0.20/0.55  fof(f69,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.55    inference(equality_resolution,[],[f61])).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f34])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.55    inference(nnf_transformation,[],[f17])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.55    inference(flattening,[],[f16])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).
% 0.20/0.55  fof(f134,plain,(
% 0.20/0.55    v1_pre_topc(k1_tsep_1(sK0,sK1,sK3))),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f36,f38,f39,f40,f43,f44,f66])).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f689,plain,(
% 0.20/0.55    k2_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))),
% 0.20/0.55    inference(forward_demodulation,[],[f688,f96])).
% 0.20/0.55  fof(f688,plain,(
% 0.20/0.55    k2_xboole_0(u1_struct_0(sK1),k2_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))),
% 0.20/0.55    inference(forward_demodulation,[],[f687,f150])).
% 0.20/0.55  fof(f687,plain,(
% 0.20/0.55    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))),
% 0.20/0.55    inference(subsumption_resolution,[],[f686,f41])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ~v2_struct_0(sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f686,plain,(
% 0.20/0.55    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) | v2_struct_0(sK2)),
% 0.20/0.55    inference(subsumption_resolution,[],[f685,f100])).
% 0.20/0.55  fof(f685,plain,(
% 0.20/0.55    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.55    inference(subsumption_resolution,[],[f684,f39])).
% 0.20/0.55  fof(f684,plain,(
% 0.20/0.55    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.55    inference(subsumption_resolution,[],[f683,f45])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    m1_pre_topc(sK1,sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f683,plain,(
% 0.20/0.55    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) | ~m1_pre_topc(sK1,sK2) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.55    inference(subsumption_resolution,[],[f682,f43])).
% 0.20/0.55  fof(f682,plain,(
% 0.20/0.55    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK2) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.55    inference(subsumption_resolution,[],[f681,f46])).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    m1_pre_topc(sK3,sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f681,plain,(
% 0.20/0.55    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK2) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.55    inference(subsumption_resolution,[],[f680,f170])).
% 0.20/0.55  fof(f170,plain,(
% 0.20/0.55    ~v2_struct_0(k1_tsep_1(sK2,sK1,sK3))),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f41,f100,f39,f45,f43,f46,f65])).
% 0.20/0.55  fof(f680,plain,(
% 0.20/0.55    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) | v2_struct_0(k1_tsep_1(sK2,sK1,sK3)) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK2) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.55    inference(subsumption_resolution,[],[f679,f178])).
% 0.20/0.55  fof(f178,plain,(
% 0.20/0.55    m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f41,f100,f39,f45,f43,f46,f67])).
% 0.20/0.55  fof(f679,plain,(
% 0.20/0.55    ~m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2) | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) | v2_struct_0(k1_tsep_1(sK2,sK1,sK3)) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK2) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.55    inference(resolution,[],[f174,f69])).
% 0.20/0.55  fof(f174,plain,(
% 0.20/0.55    v1_pre_topc(k1_tsep_1(sK2,sK1,sK3))),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f41,f100,f39,f45,f43,f46,f66])).
% 0.20/0.55  fof(f1345,plain,(
% 0.20/0.55    u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) = k2_struct_0(k1_tsep_1(sK2,sK1,sK3))),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f1315,f48])).
% 0.20/0.55  fof(f1315,plain,(
% 0.20/0.55    l1_struct_0(k1_tsep_1(sK2,sK1,sK3))),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f1176,f49])).
% 0.20/0.55  fof(f1176,plain,(
% 0.20/0.55    l1_pre_topc(k1_tsep_1(sK2,sK1,sK3))),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f100,f178,f60])).
% 0.20/0.55  fof(f1316,plain,(
% 0.20/0.55    r1_tarski(k2_struct_0(k1_tsep_1(sK2,sK1,sK3)),k2_struct_0(sK2))),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f100,f178,f1176,f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f33])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK4(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK4(X0,X1),u1_pre_topc(X1))) & ((sK4(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1)) & r2_hidden(sK5(X0,X1),u1_pre_topc(X0)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK4(X0,X1),u1_pre_topc(X1))) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X1)) | ! [X6] : (k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5 | ~r2_hidden(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))))) & ((k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X5),k2_struct_0(X1)) = X5 & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X0)) & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X5,u1_pre_topc(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f29,f32,f31,f30])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & r2_hidden(X4,u1_pre_topc(X0)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK4(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK4(X0,X1),u1_pre_topc(X1))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK4(X0,X1) & r2_hidden(X4,u1_pre_topc(X0)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK4(X0,X1),u1_pre_topc(X1))) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK4(X0,X1) & r2_hidden(X4,u1_pre_topc(X0)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (sK4(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1)) & r2_hidden(sK5(X0,X1),u1_pre_topc(X0)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5 & r2_hidden(X7,u1_pre_topc(X0)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X5),k2_struct_0(X1)) = X5 & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X0)) & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & r2_hidden(X4,u1_pre_topc(X0)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X1)) | ! [X6] : (k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5 | ~r2_hidden(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X7] : (k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5 & r2_hidden(X7,u1_pre_topc(X0)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X5,u1_pre_topc(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.56    inference(rectify,[],[f28])).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.56    inference(flattening,[],[f27])).
% 0.20/0.56  fof(f27,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.56    inference(nnf_transformation,[],[f14])).
% 0.20/0.56  fof(f14,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f2])).
% 0.20/0.56  fof(f2,axiom,(
% 0.20/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (13835)------------------------------
% 0.20/0.56  % (13835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (13835)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (13835)Memory used [KB]: 7675
% 0.20/0.56  % (13835)Time elapsed: 0.100 s
% 0.20/0.56  % (13835)------------------------------
% 0.20/0.56  % (13835)------------------------------
% 0.20/0.56  % (13819)Success in time 0.199 s
%------------------------------------------------------------------------------
