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
% DateTime   : Thu Dec  3 13:18:04 EST 2020

% Result     : Theorem 41.15s
% Output     : Refutation 41.15s
% Verified   : 
% Statistics : Number of formulae       :  113 (4781 expanded)
%              Number of leaves         :   14 (2245 expanded)
%              Depth                    :   21
%              Number of atoms          :  577 (57870 expanded)
%              Number of equality atoms :   49 ( 183 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137146,plain,(
    $false ),
    inference(subsumption_resolution,[],[f137145,f2830])).

fof(f2830,plain,(
    ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f39,f40,f179,f126,f238,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f238,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f237,f188])).

fof(f188,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f38,f39,f40,f41,f43,f42,f44,f47,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X2)
                  | k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                & ( k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f47,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f33,f32,f31,f30])).

fof(f30,plain,
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

fof(f31,plain,
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

fof(f32,plain,
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

fof(f33,plain,
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

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f44,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f42,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f43,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f41,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f237,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(unit_resulting_resolution,[],[f98,f49,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f49,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f98,plain,(
    l1_pre_topc(sK2) ),
    inference(unit_resulting_resolution,[],[f40,f44,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f126,plain,(
    m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f38,f40,f41,f42,f43,f44,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f179,plain,(
    m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) ),
    inference(unit_resulting_resolution,[],[f38,f40,f41,f42,f45,f46,f65])).

fof(f46,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f45,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f137145,plain,(
    r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    inference(forward_demodulation,[],[f137141,f6278])).

fof(f6278,plain,(
    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3)) ),
    inference(forward_demodulation,[],[f6277,f324])).

fof(f324,plain,(
    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f323,f38])).

fof(f323,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f322,f40])).

fof(f322,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f321,f41])).

fof(f321,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f320,f42])).

fof(f320,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f319,f45])).

fof(f319,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f318,f46])).

fof(f318,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f317,f167])).

fof(f167,plain,(
    ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f38,f40,f41,f42,f45,f46,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f317,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f316,f179])).

fof(f316,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f173,f66])).

fof(f66,plain,(
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
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f173,plain,(
    v1_pre_topc(k1_tsep_1(sK0,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f38,f40,f41,f42,f45,f46,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6277,plain,(
    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3)) ),
    inference(subsumption_resolution,[],[f6276,f118])).

fof(f118,plain,(
    ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f38,f40,f41,f42,f43,f44,f63])).

fof(f6276,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f6275,f542])).

fof(f542,plain,(
    l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f40,f126,f50])).

fof(f6275,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3))
    | ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f6274,f41])).

fof(f6274,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f6273,f102])).

fof(f102,plain,(
    m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f38,f39,f40,f41,f42,f43,f44,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
             => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tsep_1)).

fof(f6273,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3))
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f6272,f45])).

fof(f6272,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f6271,f219])).

fof(f219,plain,(
    m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f141,f218])).

fof(f218,plain,(
    k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK3,sK2) ),
    inference(forward_demodulation,[],[f204,f188])).

fof(f204,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f38,f39,f40,f45,f43,f46,f44,f48,f54])).

fof(f48,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f141,plain,(
    m1_pre_topc(sK3,k1_tsep_1(sK0,sK3,sK2)) ),
    inference(unit_resulting_resolution,[],[f38,f43,f44,f40,f45,f39,f46,f53])).

fof(f6271,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3))
    | ~ m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f6270,f1395])).

fof(f1395,plain,(
    ~ v2_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f41,f45,f118,f542,f102,f219,f63])).

fof(f6270,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3))
    | v2_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3))
    | ~ m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f6269,f1407])).

fof(f1407,plain,(
    m1_pre_topc(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3),k1_tsep_1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f41,f45,f118,f542,f102,f219,f65])).

fof(f6269,plain,
    ( ~ m1_pre_topc(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3),k1_tsep_1(sK0,sK1,sK2))
    | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3))
    | v2_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3))
    | ~ m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(resolution,[],[f1401,f66])).

fof(f1401,plain,(
    v1_pre_topc(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f41,f45,f118,f542,f102,f219,f64])).

fof(f137141,plain,(
    r1_tarski(u1_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f542,f1333,f1407,f1407,f254])).

fof(f254,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
      | ~ m1_pre_topc(X1,k1_tsep_1(sK0,sK1,sK2))
      | ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK2))
      | ~ m1_pre_topc(X0,X1)
      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ) ),
    inference(resolution,[],[f114,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f114,plain,(
    v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f38,f39,f40,f41,f42,f43,f44,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tmap_1)).

fof(f1333,plain,(
    m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f1321,f1329])).

fof(f1329,plain,(
    k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK2) ),
    inference(forward_demodulation,[],[f1294,f188])).

fof(f1294,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f41,f43,f47,f118,f542,f102,f114,f197,f54])).

fof(f197,plain,(
    m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f103,f196])).

fof(f196,plain,(
    k1_tsep_1(sK0,sK2,sK2) = k1_tsep_1(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f99,f188])).

fof(f99,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f38,f39,f40,f43,f44,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tmap_1)).

fof(f103,plain,(
    m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK2)) ),
    inference(unit_resulting_resolution,[],[f38,f39,f40,f43,f44,f43,f44,f53])).

fof(f1321,plain,(
    m1_pre_topc(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK2),k1_tsep_1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f41,f43,f118,f542,f102,f197,f65])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:57:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (19008)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (18995)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (19000)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (19003)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (18998)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (18993)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (18994)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (18999)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (19006)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (18994)Refutation not found, incomplete strategy% (18994)------------------------------
% 0.21/0.51  % (18994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (18994)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (18994)Memory used [KB]: 10618
% 0.21/0.51  % (18994)Time elapsed: 0.088 s
% 0.21/0.51  % (18994)------------------------------
% 0.21/0.51  % (18994)------------------------------
% 0.21/0.52  % (18997)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.52  % (18996)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (19003)Refutation not found, incomplete strategy% (19003)------------------------------
% 0.21/0.52  % (19003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19003)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (19003)Memory used [KB]: 6268
% 0.21/0.52  % (19003)Time elapsed: 0.074 s
% 0.21/0.52  % (19003)------------------------------
% 0.21/0.52  % (19003)------------------------------
% 0.21/0.52  % (19011)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.52  % (19001)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.53  % (19007)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.53  % (19002)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.53  % (19010)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.53  % (19004)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.53  % (19012)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.53  % (19013)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.53  % (19009)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.53  % (19013)Refutation not found, incomplete strategy% (19013)------------------------------
% 0.21/0.53  % (19013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (19013)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (19013)Memory used [KB]: 10618
% 0.21/0.53  % (19013)Time elapsed: 0.111 s
% 0.21/0.53  % (19013)------------------------------
% 0.21/0.53  % (19013)------------------------------
% 0.21/0.54  % (19005)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 4.03/0.91  % (19005)Time limit reached!
% 4.03/0.91  % (19005)------------------------------
% 4.03/0.91  % (19005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/0.92  % (19005)Termination reason: Time limit
% 4.48/0.93  % (18998)Time limit reached!
% 4.48/0.93  % (18998)------------------------------
% 4.48/0.93  % (18998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.48/0.93  % (19005)Termination phase: Saturation
% 4.48/0.93  
% 4.48/0.93  % (19005)Memory used [KB]: 13432
% 4.48/0.93  % (19005)Time elapsed: 0.500 s
% 4.48/0.93  % (19005)------------------------------
% 4.48/0.93  % (19005)------------------------------
% 4.48/0.94  % (18993)Time limit reached!
% 4.48/0.94  % (18993)------------------------------
% 4.48/0.94  % (18993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.48/0.94  % (18993)Termination reason: Time limit
% 4.48/0.94  
% 4.48/0.94  % (18993)Memory used [KB]: 10874
% 4.48/0.94  % (18993)Time elapsed: 0.520 s
% 4.48/0.94  % (18993)------------------------------
% 4.48/0.94  % (18993)------------------------------
% 4.48/0.95  % (18998)Termination reason: Time limit
% 4.48/0.95  % (18998)Termination phase: Saturation
% 4.48/0.95  
% 4.48/0.95  % (18998)Memory used [KB]: 8571
% 4.48/0.95  % (18998)Time elapsed: 0.500 s
% 4.48/0.95  % (18998)------------------------------
% 4.48/0.95  % (18998)------------------------------
% 5.22/1.06  % (19001)Time limit reached!
% 5.22/1.06  % (19001)------------------------------
% 5.22/1.06  % (19001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.65/1.08  % (19001)Termination reason: Time limit
% 5.65/1.08  
% 5.65/1.08  % (19001)Memory used [KB]: 9594
% 5.65/1.08  % (19001)Time elapsed: 0.621 s
% 5.65/1.08  % (19001)------------------------------
% 5.65/1.08  % (19001)------------------------------
% 7.56/1.35  % (19002)Time limit reached!
% 7.56/1.35  % (19002)------------------------------
% 7.56/1.35  % (19002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.56/1.35  % (19002)Termination reason: Time limit
% 7.56/1.35  
% 7.56/1.35  % (19002)Memory used [KB]: 22131
% 7.56/1.35  % (19002)Time elapsed: 0.926 s
% 7.56/1.35  % (19002)------------------------------
% 7.56/1.35  % (19002)------------------------------
% 9.43/1.54  % (18995)Time limit reached!
% 9.43/1.54  % (18995)------------------------------
% 9.43/1.54  % (18995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.43/1.54  % (18995)Termination reason: Time limit
% 9.43/1.54  
% 9.43/1.54  % (18995)Memory used [KB]: 19957
% 9.43/1.54  % (18995)Time elapsed: 1.120 s
% 9.43/1.54  % (18995)------------------------------
% 9.43/1.54  % (18995)------------------------------
% 10.50/1.74  % (18996)Time limit reached!
% 10.50/1.74  % (18996)------------------------------
% 10.50/1.74  % (18996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.50/1.74  % (18996)Termination reason: Time limit
% 10.50/1.74  % (18996)Termination phase: Saturation
% 10.50/1.74  
% 10.50/1.74  % (18996)Memory used [KB]: 28784
% 10.50/1.74  % (18996)Time elapsed: 1.300 s
% 10.50/1.74  % (18996)------------------------------
% 10.50/1.74  % (18996)------------------------------
% 12.91/2.04  % (18997)Time limit reached!
% 12.91/2.04  % (18997)------------------------------
% 12.91/2.04  % (18997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.91/2.04  % (18997)Termination reason: Time limit
% 12.91/2.04  % (18997)Termination phase: Saturation
% 12.91/2.04  
% 12.91/2.04  % (18997)Memory used [KB]: 18805
% 12.91/2.04  % (18997)Time elapsed: 1.600 s
% 12.91/2.04  % (18997)------------------------------
% 12.91/2.04  % (18997)------------------------------
% 14.22/2.19  % (19000)Time limit reached!
% 14.22/2.19  % (19000)------------------------------
% 14.22/2.19  % (19000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.22/2.19  % (19000)Termination reason: Time limit
% 14.22/2.19  % (19000)Termination phase: Saturation
% 14.22/2.19  
% 14.22/2.19  % (19000)Memory used [KB]: 19317
% 14.22/2.19  % (19000)Time elapsed: 1.700 s
% 14.22/2.19  % (19000)------------------------------
% 14.22/2.19  % (19000)------------------------------
% 23.61/3.33  % (19004)Time limit reached!
% 23.61/3.33  % (19004)------------------------------
% 23.61/3.33  % (19004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.61/3.33  % (19004)Termination reason: Time limit
% 23.61/3.33  % (19004)Termination phase: Saturation
% 23.61/3.33  
% 23.61/3.33  % (19004)Memory used [KB]: 70105
% 23.61/3.33  % (19004)Time elapsed: 2.900 s
% 23.61/3.33  % (19004)------------------------------
% 23.61/3.33  % (19004)------------------------------
% 41.15/5.54  % (18999)Time limit reached!
% 41.15/5.54  % (18999)------------------------------
% 41.15/5.54  % (18999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 41.15/5.54  % (18999)Termination reason: Time limit
% 41.15/5.54  % (18999)Termination phase: Saturation
% 41.15/5.54  
% 41.15/5.54  % (18999)Memory used [KB]: 44647
% 41.15/5.54  % (18999)Time elapsed: 5.100 s
% 41.15/5.54  % (18999)------------------------------
% 41.15/5.54  % (18999)------------------------------
% 41.15/5.58  % (19008)Refutation found. Thanks to Tanya!
% 41.15/5.58  % SZS status Theorem for theBenchmark
% 41.15/5.58  % SZS output start Proof for theBenchmark
% 41.15/5.58  fof(f137146,plain,(
% 41.15/5.58    $false),
% 41.15/5.58    inference(subsumption_resolution,[],[f137145,f2830])).
% 41.15/5.58  fof(f2830,plain,(
% 41.15/5.58    ~r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 41.15/5.58    inference(unit_resulting_resolution,[],[f39,f40,f179,f126,f238,f58])).
% 41.15/5.58  fof(f58,plain,(
% 41.15/5.58    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 41.15/5.58    inference(cnf_transformation,[],[f37])).
% 41.15/5.58  fof(f37,plain,(
% 41.15/5.58    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 41.15/5.58    inference(nnf_transformation,[],[f25])).
% 41.15/5.58  fof(f25,plain,(
% 41.15/5.58    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 41.15/5.58    inference(flattening,[],[f24])).
% 41.15/5.58  fof(f24,plain,(
% 41.15/5.58    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 41.15/5.58    inference(ennf_transformation,[],[f9])).
% 41.15/5.58  fof(f9,axiom,(
% 41.15/5.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 41.15/5.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 41.15/5.58  fof(f238,plain,(
% 41.15/5.58    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2))),
% 41.15/5.58    inference(forward_demodulation,[],[f237,f188])).
% 41.15/5.58  fof(f188,plain,(
% 41.15/5.58    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK1,sK2)),
% 41.15/5.58    inference(unit_resulting_resolution,[],[f38,f39,f40,f41,f43,f42,f44,f47,f54])).
% 41.15/5.58  fof(f54,plain,(
% 41.15/5.58    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | v2_struct_0(X0)) )),
% 41.15/5.58    inference(cnf_transformation,[],[f35])).
% 41.15/5.58  fof(f35,plain,(
% 41.15/5.58    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) | k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 41.15/5.58    inference(nnf_transformation,[],[f21])).
% 41.15/5.58  fof(f21,plain,(
% 41.15/5.58    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 41.15/5.58    inference(flattening,[],[f20])).
% 41.15/5.58  fof(f20,plain,(
% 41.15/5.58    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 41.15/5.58    inference(ennf_transformation,[],[f7])).
% 41.15/5.58  fof(f7,axiom,(
% 41.15/5.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))),
% 41.15/5.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tsep_1)).
% 41.15/5.58  fof(f47,plain,(
% 41.15/5.58    m1_pre_topc(sK1,sK2)),
% 41.15/5.58    inference(cnf_transformation,[],[f34])).
% 41.15/5.58  fof(f34,plain,(
% 41.15/5.58    (((~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 41.15/5.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f33,f32,f31,f30])).
% 41.15/5.58  fof(f30,plain,(
% 41.15/5.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 41.15/5.58    introduced(choice_axiom,[])).
% 41.15/5.58  fof(f31,plain,(
% 41.15/5.58    ? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 41.15/5.58    introduced(choice_axiom,[])).
% 41.15/5.58  fof(f32,plain,(
% 41.15/5.58    ? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK2) & m1_pre_topc(X3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 41.15/5.58    introduced(choice_axiom,[])).
% 41.15/5.58  fof(f33,plain,(
% 41.15/5.58    ? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK2) & m1_pre_topc(X3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 41.15/5.58    introduced(choice_axiom,[])).
% 41.15/5.58  fof(f13,plain,(
% 41.15/5.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 41.15/5.58    inference(flattening,[],[f12])).
% 41.15/5.58  fof(f12,plain,(
% 41.15/5.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & (m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 41.15/5.58    inference(ennf_transformation,[],[f11])).
% 41.15/5.58  fof(f11,negated_conjecture,(
% 41.15/5.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 41.15/5.58    inference(negated_conjecture,[],[f10])).
% 41.15/5.58  fof(f10,conjecture,(
% 41.15/5.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 41.15/5.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tmap_1)).
% 41.15/5.58  fof(f44,plain,(
% 41.15/5.58    m1_pre_topc(sK2,sK0)),
% 41.15/5.58    inference(cnf_transformation,[],[f34])).
% 41.15/5.58  fof(f42,plain,(
% 41.15/5.58    m1_pre_topc(sK1,sK0)),
% 41.15/5.58    inference(cnf_transformation,[],[f34])).
% 41.15/5.58  fof(f43,plain,(
% 41.15/5.58    ~v2_struct_0(sK2)),
% 41.15/5.58    inference(cnf_transformation,[],[f34])).
% 41.15/5.58  fof(f41,plain,(
% 41.15/5.58    ~v2_struct_0(sK1)),
% 41.15/5.58    inference(cnf_transformation,[],[f34])).
% 41.15/5.58  fof(f38,plain,(
% 41.15/5.58    ~v2_struct_0(sK0)),
% 41.15/5.58    inference(cnf_transformation,[],[f34])).
% 41.15/5.58  fof(f237,plain,(
% 41.15/5.58    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 41.15/5.58    inference(unit_resulting_resolution,[],[f98,f49,f51])).
% 41.15/5.58  fof(f51,plain,(
% 41.15/5.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0)) )),
% 41.15/5.58    inference(cnf_transformation,[],[f15])).
% 41.15/5.58  fof(f15,plain,(
% 41.15/5.58    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 41.15/5.58    inference(ennf_transformation,[],[f2])).
% 41.15/5.58  fof(f2,axiom,(
% 41.15/5.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 41.15/5.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).
% 41.15/5.58  fof(f49,plain,(
% 41.15/5.58    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)),
% 41.15/5.58    inference(cnf_transformation,[],[f34])).
% 41.15/5.58  fof(f98,plain,(
% 41.15/5.58    l1_pre_topc(sK2)),
% 41.15/5.58    inference(unit_resulting_resolution,[],[f40,f44,f50])).
% 41.15/5.58  fof(f50,plain,(
% 41.15/5.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 41.15/5.58    inference(cnf_transformation,[],[f14])).
% 41.15/5.58  fof(f14,plain,(
% 41.15/5.58    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 41.15/5.58    inference(ennf_transformation,[],[f1])).
% 41.15/5.58  fof(f1,axiom,(
% 41.15/5.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 41.15/5.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 41.15/5.58  fof(f126,plain,(
% 41.15/5.58    m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)),
% 41.15/5.58    inference(unit_resulting_resolution,[],[f38,f40,f41,f42,f43,f44,f65])).
% 41.15/5.58  fof(f65,plain,(
% 41.15/5.58    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | v2_struct_0(X0)) )),
% 41.15/5.58    inference(cnf_transformation,[],[f29])).
% 41.15/5.58  fof(f29,plain,(
% 41.15/5.58    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 41.15/5.58    inference(flattening,[],[f28])).
% 41.15/5.58  fof(f28,plain,(
% 41.15/5.58    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 41.15/5.58    inference(ennf_transformation,[],[f4])).
% 41.15/5.58  fof(f4,axiom,(
% 41.15/5.58    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 41.15/5.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 41.15/5.58  fof(f179,plain,(
% 41.15/5.58    m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)),
% 41.15/5.58    inference(unit_resulting_resolution,[],[f38,f40,f41,f42,f45,f46,f65])).
% 41.15/5.58  fof(f46,plain,(
% 41.15/5.58    m1_pre_topc(sK3,sK0)),
% 41.15/5.58    inference(cnf_transformation,[],[f34])).
% 41.15/5.58  fof(f45,plain,(
% 41.15/5.58    ~v2_struct_0(sK3)),
% 41.15/5.58    inference(cnf_transformation,[],[f34])).
% 41.15/5.58  fof(f40,plain,(
% 41.15/5.58    l1_pre_topc(sK0)),
% 41.15/5.58    inference(cnf_transformation,[],[f34])).
% 41.15/5.58  fof(f39,plain,(
% 41.15/5.58    v2_pre_topc(sK0)),
% 41.15/5.58    inference(cnf_transformation,[],[f34])).
% 41.15/5.58  fof(f137145,plain,(
% 41.15/5.58    r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 41.15/5.58    inference(forward_demodulation,[],[f137141,f6278])).
% 41.15/5.58  fof(f6278,plain,(
% 41.15/5.58    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3))),
% 41.15/5.58    inference(forward_demodulation,[],[f6277,f324])).
% 41.15/5.58  fof(f324,plain,(
% 41.15/5.58    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))),
% 41.15/5.58    inference(subsumption_resolution,[],[f323,f38])).
% 41.15/5.58  fof(f323,plain,(
% 41.15/5.58    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | v2_struct_0(sK0)),
% 41.15/5.58    inference(subsumption_resolution,[],[f322,f40])).
% 41.15/5.58  fof(f322,plain,(
% 41.15/5.58    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 41.15/5.58    inference(subsumption_resolution,[],[f321,f41])).
% 41.15/5.58  fof(f321,plain,(
% 41.15/5.58    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 41.15/5.58    inference(subsumption_resolution,[],[f320,f42])).
% 41.15/5.58  fof(f320,plain,(
% 41.15/5.58    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 41.15/5.58    inference(subsumption_resolution,[],[f319,f45])).
% 41.15/5.58  fof(f319,plain,(
% 41.15/5.58    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 41.15/5.58    inference(subsumption_resolution,[],[f318,f46])).
% 41.15/5.58  fof(f318,plain,(
% 41.15/5.58    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 41.15/5.58    inference(subsumption_resolution,[],[f317,f167])).
% 41.15/5.58  fof(f167,plain,(
% 41.15/5.58    ~v2_struct_0(k1_tsep_1(sK0,sK1,sK3))),
% 41.15/5.58    inference(unit_resulting_resolution,[],[f38,f40,f41,f42,f45,f46,f63])).
% 41.15/5.58  fof(f63,plain,(
% 41.15/5.58    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 41.15/5.58    inference(cnf_transformation,[],[f29])).
% 41.15/5.58  fof(f317,plain,(
% 41.15/5.58    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 41.15/5.58    inference(subsumption_resolution,[],[f316,f179])).
% 41.15/5.58  fof(f316,plain,(
% 41.15/5.58    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 41.15/5.58    inference(resolution,[],[f173,f66])).
% 41.15/5.58  fof(f66,plain,(
% 41.15/5.58    ( ! [X2,X0,X1] : (~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 41.15/5.58    inference(equality_resolution,[],[f56])).
% 41.15/5.58  fof(f56,plain,(
% 41.15/5.58    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 41.15/5.58    inference(cnf_transformation,[],[f36])).
% 41.15/5.58  fof(f36,plain,(
% 41.15/5.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 41.15/5.58    inference(nnf_transformation,[],[f23])).
% 41.15/5.58  fof(f23,plain,(
% 41.15/5.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 41.15/5.58    inference(flattening,[],[f22])).
% 41.15/5.58  fof(f22,plain,(
% 41.15/5.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 41.15/5.58    inference(ennf_transformation,[],[f3])).
% 41.15/5.58  fof(f3,axiom,(
% 41.15/5.58    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 41.15/5.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).
% 41.15/5.58  fof(f173,plain,(
% 41.15/5.58    v1_pre_topc(k1_tsep_1(sK0,sK1,sK3))),
% 41.15/5.58    inference(unit_resulting_resolution,[],[f38,f40,f41,f42,f45,f46,f64])).
% 41.15/5.58  fof(f64,plain,(
% 41.15/5.58    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 41.15/5.58    inference(cnf_transformation,[],[f29])).
% 41.15/5.58  fof(f6277,plain,(
% 41.15/5.58    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3))),
% 41.15/5.58    inference(subsumption_resolution,[],[f6276,f118])).
% 41.15/5.58  fof(f118,plain,(
% 41.15/5.58    ~v2_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 41.15/5.58    inference(unit_resulting_resolution,[],[f38,f40,f41,f42,f43,f44,f63])).
% 41.15/5.58  fof(f6276,plain,(
% 41.15/5.58    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 41.15/5.58    inference(subsumption_resolution,[],[f6275,f542])).
% 41.15/5.58  fof(f542,plain,(
% 41.15/5.58    l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))),
% 41.15/5.58    inference(unit_resulting_resolution,[],[f40,f126,f50])).
% 41.15/5.58  fof(f6275,plain,(
% 41.15/5.58    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3)) | ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 41.15/5.58    inference(subsumption_resolution,[],[f6274,f41])).
% 41.15/5.58  fof(f6274,plain,(
% 41.15/5.58    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3)) | v2_struct_0(sK1) | ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 41.15/5.58    inference(subsumption_resolution,[],[f6273,f102])).
% 41.15/5.58  fof(f102,plain,(
% 41.15/5.58    m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))),
% 41.15/5.58    inference(unit_resulting_resolution,[],[f38,f39,f40,f41,f42,f43,f44,f53])).
% 41.15/5.58  fof(f53,plain,(
% 41.15/5.58    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | v2_struct_0(X0)) )),
% 41.15/5.58    inference(cnf_transformation,[],[f19])).
% 41.15/5.58  fof(f19,plain,(
% 41.15/5.58    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 41.15/5.58    inference(flattening,[],[f18])).
% 41.15/5.58  fof(f18,plain,(
% 41.15/5.58    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 41.15/5.58    inference(ennf_transformation,[],[f6])).
% 41.15/5.58  fof(f6,axiom,(
% 41.15/5.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)))))),
% 41.15/5.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tsep_1)).
% 41.15/5.58  fof(f6273,plain,(
% 41.15/5.58    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3)) | ~m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK1) | ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 41.15/5.58    inference(subsumption_resolution,[],[f6272,f45])).
% 41.15/5.58  fof(f6272,plain,(
% 41.15/5.58    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3)) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK1) | ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 41.15/5.58    inference(subsumption_resolution,[],[f6271,f219])).
% 41.15/5.58  fof(f219,plain,(
% 41.15/5.58    m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK2))),
% 41.15/5.58    inference(backward_demodulation,[],[f141,f218])).
% 41.15/5.58  fof(f218,plain,(
% 41.15/5.58    k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK3,sK2)),
% 41.15/5.58    inference(forward_demodulation,[],[f204,f188])).
% 41.15/5.58  fof(f204,plain,(
% 41.15/5.58    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK3,sK2)),
% 41.15/5.58    inference(unit_resulting_resolution,[],[f38,f39,f40,f45,f43,f46,f44,f48,f54])).
% 41.15/5.58  fof(f48,plain,(
% 41.15/5.58    m1_pre_topc(sK3,sK2)),
% 41.15/5.58    inference(cnf_transformation,[],[f34])).
% 41.15/5.58  fof(f141,plain,(
% 41.15/5.58    m1_pre_topc(sK3,k1_tsep_1(sK0,sK3,sK2))),
% 41.15/5.58    inference(unit_resulting_resolution,[],[f38,f43,f44,f40,f45,f39,f46,f53])).
% 41.15/5.58  fof(f6271,plain,(
% 41.15/5.58    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3)) | ~m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK1) | ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 41.15/5.58    inference(subsumption_resolution,[],[f6270,f1395])).
% 41.15/5.58  fof(f1395,plain,(
% 41.15/5.58    ~v2_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3))),
% 41.15/5.58    inference(unit_resulting_resolution,[],[f41,f45,f118,f542,f102,f219,f63])).
% 41.15/5.58  fof(f6270,plain,(
% 41.15/5.58    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3)) | v2_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3)) | ~m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK1) | ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 41.15/5.58    inference(subsumption_resolution,[],[f6269,f1407])).
% 41.15/5.58  fof(f1407,plain,(
% 41.15/5.58    m1_pre_topc(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3),k1_tsep_1(sK0,sK1,sK2))),
% 41.15/5.58    inference(unit_resulting_resolution,[],[f41,f45,f118,f542,f102,f219,f65])).
% 41.15/5.58  fof(f6269,plain,(
% 41.15/5.58    ~m1_pre_topc(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3),k1_tsep_1(sK0,sK1,sK2)) | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3)) | v2_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3)) | ~m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK1) | ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 41.15/5.58    inference(resolution,[],[f1401,f66])).
% 41.15/5.58  fof(f1401,plain,(
% 41.15/5.58    v1_pre_topc(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3))),
% 41.15/5.58    inference(unit_resulting_resolution,[],[f41,f45,f118,f542,f102,f219,f64])).
% 41.15/5.58  fof(f137141,plain,(
% 41.15/5.58    r1_tarski(u1_struct_0(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 41.15/5.58    inference(unit_resulting_resolution,[],[f542,f1333,f1407,f1407,f254])).
% 41.15/5.58  fof(f254,plain,(
% 41.15/5.58    ( ! [X0,X1] : (~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(X1,k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(X0,X1) | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))) )),
% 41.15/5.58    inference(resolution,[],[f114,f59])).
% 41.15/5.58  fof(f59,plain,(
% 41.15/5.58    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 41.15/5.58    inference(cnf_transformation,[],[f37])).
% 41.15/5.58  fof(f114,plain,(
% 41.15/5.58    v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))),
% 41.15/5.58    inference(unit_resulting_resolution,[],[f38,f39,f40,f41,f42,f43,f44,f62])).
% 41.15/5.58  fof(f62,plain,(
% 41.15/5.58    ( ! [X2,X0,X1] : (v2_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 41.15/5.58    inference(cnf_transformation,[],[f27])).
% 41.15/5.58  fof(f27,plain,(
% 41.15/5.58    ! [X0,X1,X2] : ((v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 41.15/5.58    inference(flattening,[],[f26])).
% 41.15/5.58  fof(f26,plain,(
% 41.15/5.58    ! [X0,X1,X2] : ((v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 41.15/5.58    inference(ennf_transformation,[],[f5])).
% 41.15/5.58  fof(f5,axiom,(
% 41.15/5.58    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 41.15/5.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tmap_1)).
% 41.15/5.58  fof(f1333,plain,(
% 41.15/5.58    m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK1,sK2))),
% 41.15/5.58    inference(backward_demodulation,[],[f1321,f1329])).
% 41.15/5.58  fof(f1329,plain,(
% 41.15/5.58    k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK2)),
% 41.15/5.58    inference(forward_demodulation,[],[f1294,f188])).
% 41.15/5.58  fof(f1294,plain,(
% 41.15/5.58    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK2)),
% 41.15/5.58    inference(unit_resulting_resolution,[],[f41,f43,f47,f118,f542,f102,f114,f197,f54])).
% 41.15/5.58  fof(f197,plain,(
% 41.15/5.58    m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2))),
% 41.15/5.58    inference(backward_demodulation,[],[f103,f196])).
% 41.15/5.58  fof(f196,plain,(
% 41.15/5.58    k1_tsep_1(sK0,sK2,sK2) = k1_tsep_1(sK0,sK1,sK2)),
% 41.15/5.58    inference(backward_demodulation,[],[f99,f188])).
% 41.15/5.58  fof(f99,plain,(
% 41.15/5.58    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)),
% 41.15/5.58    inference(unit_resulting_resolution,[],[f38,f39,f40,f43,f44,f52])).
% 41.15/5.58  fof(f52,plain,(
% 41.15/5.58    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | v2_struct_0(X0)) )),
% 41.15/5.58    inference(cnf_transformation,[],[f17])).
% 41.15/5.58  fof(f17,plain,(
% 41.15/5.58    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 41.15/5.58    inference(flattening,[],[f16])).
% 41.15/5.58  fof(f16,plain,(
% 41.15/5.58    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 41.15/5.58    inference(ennf_transformation,[],[f8])).
% 41.15/5.58  fof(f8,axiom,(
% 41.15/5.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 41.15/5.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tmap_1)).
% 41.15/5.58  fof(f103,plain,(
% 41.15/5.58    m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK2))),
% 41.15/5.58    inference(unit_resulting_resolution,[],[f38,f39,f40,f43,f44,f43,f44,f53])).
% 41.15/5.58  fof(f1321,plain,(
% 41.15/5.58    m1_pre_topc(k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK2),k1_tsep_1(sK0,sK1,sK2))),
% 41.15/5.58    inference(unit_resulting_resolution,[],[f41,f43,f118,f542,f102,f197,f65])).
% 41.15/5.58  % SZS output end Proof for theBenchmark
% 41.15/5.58  % (19008)------------------------------
% 41.15/5.58  % (19008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 41.15/5.58  % (19008)Termination reason: Refutation
% 41.15/5.58  
% 41.15/5.58  % (19008)Memory used [KB]: 104902
% 41.15/5.58  % (19008)Time elapsed: 5.099 s
% 41.15/5.58  % (19008)------------------------------
% 41.15/5.58  % (19008)------------------------------
% 41.67/5.59  % (18992)Success in time 5.224 s
%------------------------------------------------------------------------------
