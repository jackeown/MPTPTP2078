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
% DateTime   : Thu Dec  3 13:23:11 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  128 (1037 expanded)
%              Number of leaves         :   15 ( 434 expanded)
%              Depth                    :   30
%              Number of atoms          :  561 (6869 expanded)
%              Number of equality atoms :   35 ( 194 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1135,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1131,f127])).

fof(f127,plain,(
    r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f126,f115])).

fof(f115,plain,(
    sK2 = sK4(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f114,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))
    & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    & m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f28,f27,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                    & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
                & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,X1))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,X1)))
                & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,X1))) )
            & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,X1))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,sK1)))
              & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1))) )
          & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,sK1))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,sK1)))
            & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1))) )
        & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,sK1))) )
   => ( ? [X3] :
          ( ~ m1_subset_1(k2_xboole_0(sK2,X3),u1_struct_0(k9_yellow_6(sK0,sK1)))
          & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1))) )
      & m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X3] :
        ( ~ m1_subset_1(k2_xboole_0(sK2,X3),u1_struct_0(k9_yellow_6(sK0,sK1)))
        & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1))) )
   => ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))
      & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
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
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                   => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                 => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_waybel_9)).

fof(f114,plain,
    ( sK2 = sK4(sK0,sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f113,f41])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f113,plain,
    ( sK2 = sK4(sK0,sK1,sK2)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f112,f42])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f112,plain,
    ( sK2 = sK4(sK0,sK1,sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f109,f43])).

fof(f43,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f109,plain,
    ( sK2 = sK4(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f51,f44])).

fof(f44,plain,(
    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | sK4(X0,X1,X2) = X2
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_pre_topc(sK4(X0,X1,X2),X0)
                & r2_hidden(X1,sK4(X0,X1,X2))
                & sK4(X0,X1,X2) = X2
                & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( v3_pre_topc(X3,X0)
          & r2_hidden(X1,X3)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_pre_topc(sK4(X0,X1,X2),X0)
        & r2_hidden(X1,sK4(X0,X1,X2))
        & sK4(X0,X1,X2) = X2
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
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
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_yellow_6)).

fof(f126,plain,(
    r2_hidden(sK1,sK4(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f125,f40])).

fof(f125,plain,
    ( r2_hidden(sK1,sK4(sK0,sK1,sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f124,f41])).

fof(f124,plain,
    ( r2_hidden(sK1,sK4(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f123,f42])).

fof(f123,plain,
    ( r2_hidden(sK1,sK4(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f120,f43])).

fof(f120,plain,
    ( r2_hidden(sK1,sK4(sK0,sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f52,f44])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | r2_hidden(X1,sK4(X0,X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1131,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f1130,f68])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & ~ r2_hidden(sK5(X0,X1,X2),X0) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( r2_hidden(sK5(X0,X1,X2),X1)
            | r2_hidden(sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & ~ r2_hidden(sK5(X0,X1,X2),X0) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( r2_hidden(sK5(X0,X1,X2),X1)
          | r2_hidden(sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f1130,plain,(
    ~ r2_hidden(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f1129,f41])).

fof(f1129,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(sK2,sK3))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1128,f42])).

fof(f1128,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(sK2,sK3))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1127,f139])).

fof(f139,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(subsumption_resolution,[],[f138,f40])).

fof(f138,plain,
    ( v3_pre_topc(sK2,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f137,f41])).

fof(f137,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f136,f42])).

fof(f136,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f135,f43])).

fof(f135,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f133,f44])).

fof(f133,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f53,f115])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK4(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1127,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(sK2,sK3))
    | ~ v3_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1126,f482])).

fof(f482,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f481,f40])).

fof(f481,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f480,f41])).

fof(f480,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f479,f42])).

fof(f479,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f478,f43])).

fof(f478,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f476,f44])).

fof(f476,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f50,f115])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1126,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(sK2,sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1125,f144])).

fof(f144,plain,(
    v3_pre_topc(sK3,sK0) ),
    inference(subsumption_resolution,[],[f143,f40])).

fof(f143,plain,
    ( v3_pre_topc(sK3,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f142,f41])).

fof(f142,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f141,f42])).

fof(f141,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f140,f43])).

fof(f140,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f134,f45])).

fof(f45,plain,(
    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f134,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f53,f119])).

fof(f119,plain,(
    sK3 = sK4(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f118,f40])).

fof(f118,plain,
    ( sK3 = sK4(sK0,sK1,sK3)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f117,f41])).

fof(f117,plain,
    ( sK3 = sK4(sK0,sK1,sK3)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f116,f42])).

fof(f116,plain,
    ( sK3 = sK4(sK0,sK1,sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f110,f43])).

fof(f110,plain,
    ( sK3 = sK4(sK0,sK1,sK3)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f51,f45])).

fof(f1125,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(sK2,sK3))
    | ~ v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1122,f487])).

fof(f487,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f486,f40])).

fof(f486,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f485,f41])).

fof(f485,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f484,f42])).

fof(f484,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f483,f43])).

fof(f483,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f477,f45])).

fof(f477,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f50,f119])).

fof(f1122,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f1121,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_tops_1)).

fof(f1121,plain,
    ( ~ v3_pre_topc(k2_xboole_0(sK2,sK3),sK0)
    | ~ r2_hidden(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f1120,f490])).

fof(f490,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f482,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1120,plain,
    ( ~ v3_pre_topc(k2_xboole_0(sK2,sK3),sK0)
    | ~ r2_hidden(sK1,k2_xboole_0(sK2,sK3))
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f1116,f495])).

fof(f495,plain,(
    r1_tarski(sK3,u1_struct_0(sK0)) ),
    inference(resolution,[],[f487,f56])).

fof(f1116,plain,
    ( ~ v3_pre_topc(k2_xboole_0(sK2,sK3),sK0)
    | ~ r2_hidden(sK1,k2_xboole_0(sK2,sK3))
    | ~ r1_tarski(sK3,u1_struct_0(sK0))
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f1111,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f1111,plain,
    ( ~ r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0))
    | ~ v3_pre_topc(k2_xboole_0(sK2,sK3),sK0)
    | ~ r2_hidden(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(resolution,[],[f879,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f879,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k2_xboole_0(sK2,sK3))
    | ~ v3_pre_topc(k2_xboole_0(sK2,sK3),sK0) ),
    inference(subsumption_resolution,[],[f878,f40])).

fof(f878,plain,
    ( ~ v3_pre_topc(k2_xboole_0(sK2,sK3),sK0)
    | ~ r2_hidden(sK1,k2_xboole_0(sK2,sK3))
    | ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f877,f41])).

fof(f877,plain,
    ( ~ v3_pre_topc(k2_xboole_0(sK2,sK3),sK0)
    | ~ r2_hidden(sK1,k2_xboole_0(sK2,sK3))
    | ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f876,f42])).

fof(f876,plain,
    ( ~ v3_pre_topc(k2_xboole_0(sK2,sK3),sK0)
    | ~ r2_hidden(sK1,k2_xboole_0(sK2,sK3))
    | ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f869,f43])).

fof(f869,plain,
    ( ~ v3_pre_topc(k2_xboole_0(sK2,sK3),sK0)
    | ~ r2_hidden(sK1,k2_xboole_0(sK2,sK3))
    | ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f49,f186])).

fof(f186,plain,(
    ~ r2_hidden(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(resolution,[],[f168,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(k9_yellow_6(sK0,sK1)))
      | ~ r2_hidden(k2_xboole_0(sK2,sK3),X0) ) ),
    inference(resolution,[],[f73,f46])).

fof(f46,plain,(
    ~ m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X2)
      | ~ r1_tarski(X2,X1) ) ),
    inference(resolution,[],[f60,f57])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f168,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f54,f167])).

fof(f167,plain,(
    ! [X21] : k2_xboole_0(X21,X21) = X21 ),
    inference(subsumption_resolution,[],[f166,f156])).

fof(f156,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1,X1),X0)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(subsumption_resolution,[],[f152,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X2)
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f152,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1,X1),X1)
      | r2_hidden(sK5(X0,X1,X1),X0)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(factoring,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X0)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f166,plain,(
    ! [X21] :
      ( k2_xboole_0(X21,X21) = X21
      | ~ r2_hidden(sK5(X21,X21,X21),X21) ) ),
    inference(duplicate_literal_removal,[],[f163])).

fof(f163,plain,(
    ! [X21] :
      ( k2_xboole_0(X21,X21) = X21
      | ~ r2_hidden(sK5(X21,X21,X21),X21)
      | k2_xboole_0(X21,X21) = X21 ) ),
    inference(resolution,[],[f156,f66])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v3_pre_topc(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
                  | ~ v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X1,X2) )
                & ( ( v3_pre_topc(X2,X0)
                    & r2_hidden(X1,X2) )
                  | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
                  | ~ v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X1,X2) )
                & ( ( v3_pre_topc(X2,X0)
                    & r2_hidden(X1,X2) )
                  | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:24:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (6532)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (6527)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (6525)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (6529)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (6525)Refutation not found, incomplete strategy% (6525)------------------------------
% 0.21/0.48  % (6525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (6541)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (6525)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (6525)Memory used [KB]: 10618
% 0.21/0.49  % (6525)Time elapsed: 0.061 s
% 0.21/0.49  % (6525)------------------------------
% 0.21/0.49  % (6525)------------------------------
% 0.21/0.49  % (6538)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (6530)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (6534)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (6537)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (6531)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (6540)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (6542)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (6535)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (6524)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (6528)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (6544)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (6539)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (6543)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (6544)Refutation not found, incomplete strategy% (6544)------------------------------
% 0.21/0.50  % (6544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (6544)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (6544)Memory used [KB]: 10618
% 0.21/0.50  % (6544)Time elapsed: 0.099 s
% 0.21/0.50  % (6544)------------------------------
% 0.21/0.50  % (6544)------------------------------
% 0.21/0.51  % (6536)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (6526)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (6533)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.50/0.57  % (6542)Refutation found. Thanks to Tanya!
% 1.50/0.57  % SZS status Theorem for theBenchmark
% 1.50/0.57  % SZS output start Proof for theBenchmark
% 1.50/0.57  fof(f1135,plain,(
% 1.50/0.57    $false),
% 1.50/0.57    inference(subsumption_resolution,[],[f1131,f127])).
% 1.50/0.57  fof(f127,plain,(
% 1.50/0.57    r2_hidden(sK1,sK2)),
% 1.50/0.57    inference(forward_demodulation,[],[f126,f115])).
% 1.50/0.57  fof(f115,plain,(
% 1.50/0.57    sK2 = sK4(sK0,sK1,sK2)),
% 1.50/0.57    inference(subsumption_resolution,[],[f114,f40])).
% 1.50/0.57  fof(f40,plain,(
% 1.50/0.57    ~v2_struct_0(sK0)),
% 1.50/0.57    inference(cnf_transformation,[],[f29])).
% 1.50/0.57  fof(f29,plain,(
% 1.50/0.57    (((~m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.50/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f28,f27,f26,f25])).
% 1.50/0.57  fof(f25,plain,(
% 1.50/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,X1)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.50/0.57    introduced(choice_axiom,[])).
% 1.50/0.57  fof(f26,plain,(
% 1.50/0.57    ? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,X1)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 1.50/0.57    introduced(choice_axiom,[])).
% 1.50/0.57  fof(f27,plain,(
% 1.50/0.57    ? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,sK1)))) => (? [X3] : (~m1_subset_1(k2_xboole_0(sK2,X3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))))),
% 1.50/0.57    introduced(choice_axiom,[])).
% 1.50/0.57  fof(f28,plain,(
% 1.50/0.57    ? [X3] : (~m1_subset_1(k2_xboole_0(sK2,X3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1)))) => (~m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))))),
% 1.50/0.57    introduced(choice_axiom,[])).
% 1.50/0.57  fof(f13,plain,(
% 1.50/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.50/0.57    inference(flattening,[],[f12])).
% 1.50/0.57  fof(f12,plain,(
% 1.50/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.50/0.57    inference(ennf_transformation,[],[f11])).
% 1.50/0.57  fof(f11,negated_conjecture,(
% 1.50/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 1.50/0.57    inference(negated_conjecture,[],[f10])).
% 1.50/0.57  fof(f10,conjecture,(
% 1.50/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_waybel_9)).
% 1.50/0.57  fof(f114,plain,(
% 1.50/0.57    sK2 = sK4(sK0,sK1,sK2) | v2_struct_0(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f113,f41])).
% 1.50/0.57  fof(f41,plain,(
% 1.50/0.57    v2_pre_topc(sK0)),
% 1.50/0.57    inference(cnf_transformation,[],[f29])).
% 1.50/0.57  fof(f113,plain,(
% 1.50/0.57    sK2 = sK4(sK0,sK1,sK2) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f112,f42])).
% 1.50/0.57  fof(f42,plain,(
% 1.50/0.57    l1_pre_topc(sK0)),
% 1.50/0.57    inference(cnf_transformation,[],[f29])).
% 1.50/0.57  fof(f112,plain,(
% 1.50/0.57    sK2 = sK4(sK0,sK1,sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f109,f43])).
% 1.50/0.57  fof(f43,plain,(
% 1.50/0.57    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.50/0.57    inference(cnf_transformation,[],[f29])).
% 1.50/0.57  fof(f109,plain,(
% 1.50/0.57    sK2 = sK4(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(resolution,[],[f51,f44])).
% 1.50/0.57  fof(f44,plain,(
% 1.50/0.57    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.50/0.57    inference(cnf_transformation,[],[f29])).
% 1.50/0.57  fof(f51,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | sK4(X0,X1,X2) = X2 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f33])).
% 1.50/0.57  fof(f33,plain,(
% 1.50/0.57    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(sK4(X0,X1,X2),X0) & r2_hidden(X1,sK4(X0,X1,X2)) & sK4(X0,X1,X2) = X2 & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.50/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f32])).
% 1.50/0.57  fof(f32,plain,(
% 1.50/0.57    ! [X2,X1,X0] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_pre_topc(sK4(X0,X1,X2),X0) & r2_hidden(X1,sK4(X0,X1,X2)) & sK4(X0,X1,X2) = X2 & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.50/0.57    introduced(choice_axiom,[])).
% 1.50/0.57  fof(f17,plain,(
% 1.50/0.57    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.50/0.57    inference(flattening,[],[f16])).
% 1.50/0.57  fof(f16,plain,(
% 1.50/0.57    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.50/0.57    inference(ennf_transformation,[],[f8])).
% 1.50/0.57  fof(f8,axiom,(
% 1.50/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_yellow_6)).
% 1.50/0.57  fof(f126,plain,(
% 1.50/0.57    r2_hidden(sK1,sK4(sK0,sK1,sK2))),
% 1.50/0.57    inference(subsumption_resolution,[],[f125,f40])).
% 1.50/0.57  fof(f125,plain,(
% 1.50/0.57    r2_hidden(sK1,sK4(sK0,sK1,sK2)) | v2_struct_0(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f124,f41])).
% 1.50/0.57  fof(f124,plain,(
% 1.50/0.57    r2_hidden(sK1,sK4(sK0,sK1,sK2)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f123,f42])).
% 1.50/0.57  fof(f123,plain,(
% 1.50/0.57    r2_hidden(sK1,sK4(sK0,sK1,sK2)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f120,f43])).
% 1.50/0.57  fof(f120,plain,(
% 1.50/0.57    r2_hidden(sK1,sK4(sK0,sK1,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(resolution,[],[f52,f44])).
% 1.50/0.57  fof(f52,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | r2_hidden(X1,sK4(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f33])).
% 1.50/0.57  fof(f1131,plain,(
% 1.50/0.57    ~r2_hidden(sK1,sK2)),
% 1.50/0.57    inference(resolution,[],[f1130,f68])).
% 1.50/0.57  fof(f68,plain,(
% 1.50/0.57    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 1.50/0.57    inference(equality_resolution,[],[f62])).
% 1.50/0.57  fof(f62,plain,(
% 1.50/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 1.50/0.57    inference(cnf_transformation,[],[f39])).
% 1.50/0.57  fof(f39,plain,(
% 1.50/0.57    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.50/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).
% 1.50/0.57  fof(f38,plain,(
% 1.50/0.57    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.50/0.57    introduced(choice_axiom,[])).
% 1.50/0.57  fof(f37,plain,(
% 1.50/0.57    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.50/0.57    inference(rectify,[],[f36])).
% 1.50/0.57  fof(f36,plain,(
% 1.50/0.57    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.50/0.57    inference(flattening,[],[f35])).
% 1.50/0.57  fof(f35,plain,(
% 1.50/0.57    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.50/0.57    inference(nnf_transformation,[],[f1])).
% 1.50/0.57  fof(f1,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.50/0.57  fof(f1130,plain,(
% 1.50/0.57    ~r2_hidden(sK1,k2_xboole_0(sK2,sK3))),
% 1.50/0.57    inference(subsumption_resolution,[],[f1129,f41])).
% 1.50/0.57  fof(f1129,plain,(
% 1.50/0.57    ~r2_hidden(sK1,k2_xboole_0(sK2,sK3)) | ~v2_pre_topc(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f1128,f42])).
% 1.50/0.57  fof(f1128,plain,(
% 1.50/0.57    ~r2_hidden(sK1,k2_xboole_0(sK2,sK3)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f1127,f139])).
% 1.50/0.57  fof(f139,plain,(
% 1.50/0.57    v3_pre_topc(sK2,sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f138,f40])).
% 1.50/0.57  fof(f138,plain,(
% 1.50/0.57    v3_pre_topc(sK2,sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f137,f41])).
% 1.50/0.57  fof(f137,plain,(
% 1.50/0.57    v3_pre_topc(sK2,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f136,f42])).
% 1.50/0.57  fof(f136,plain,(
% 1.50/0.57    v3_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f135,f43])).
% 1.50/0.57  fof(f135,plain,(
% 1.50/0.57    v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f133,f44])).
% 1.50/0.57  fof(f133,plain,(
% 1.50/0.57    v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(superposition,[],[f53,f115])).
% 1.50/0.57  fof(f53,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (v3_pre_topc(sK4(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f33])).
% 1.50/0.57  fof(f1127,plain,(
% 1.50/0.57    ~r2_hidden(sK1,k2_xboole_0(sK2,sK3)) | ~v3_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f1126,f482])).
% 1.50/0.57  fof(f482,plain,(
% 1.50/0.57    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.50/0.57    inference(subsumption_resolution,[],[f481,f40])).
% 1.50/0.57  fof(f481,plain,(
% 1.50/0.57    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f480,f41])).
% 1.50/0.57  fof(f480,plain,(
% 1.50/0.57    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f479,f42])).
% 1.50/0.57  fof(f479,plain,(
% 1.50/0.57    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f478,f43])).
% 1.50/0.57  fof(f478,plain,(
% 1.50/0.57    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f476,f44])).
% 1.50/0.57  fof(f476,plain,(
% 1.50/0.57    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(superposition,[],[f50,f115])).
% 1.50/0.57  fof(f50,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f33])).
% 1.50/0.57  fof(f1126,plain,(
% 1.50/0.57    ~r2_hidden(sK1,k2_xboole_0(sK2,sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f1125,f144])).
% 1.50/0.57  fof(f144,plain,(
% 1.50/0.57    v3_pre_topc(sK3,sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f143,f40])).
% 1.50/0.57  fof(f143,plain,(
% 1.50/0.57    v3_pre_topc(sK3,sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f142,f41])).
% 1.50/0.57  fof(f142,plain,(
% 1.50/0.57    v3_pre_topc(sK3,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f141,f42])).
% 1.50/0.57  fof(f141,plain,(
% 1.50/0.57    v3_pre_topc(sK3,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f140,f43])).
% 1.50/0.57  fof(f140,plain,(
% 1.50/0.57    v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f134,f45])).
% 1.50/0.57  fof(f45,plain,(
% 1.50/0.57    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.50/0.57    inference(cnf_transformation,[],[f29])).
% 1.50/0.57  fof(f134,plain,(
% 1.50/0.57    v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(superposition,[],[f53,f119])).
% 1.50/0.57  fof(f119,plain,(
% 1.50/0.57    sK3 = sK4(sK0,sK1,sK3)),
% 1.50/0.57    inference(subsumption_resolution,[],[f118,f40])).
% 1.50/0.57  fof(f118,plain,(
% 1.50/0.57    sK3 = sK4(sK0,sK1,sK3) | v2_struct_0(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f117,f41])).
% 1.50/0.57  fof(f117,plain,(
% 1.50/0.57    sK3 = sK4(sK0,sK1,sK3) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f116,f42])).
% 1.50/0.57  fof(f116,plain,(
% 1.50/0.57    sK3 = sK4(sK0,sK1,sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f110,f43])).
% 1.50/0.57  fof(f110,plain,(
% 1.50/0.57    sK3 = sK4(sK0,sK1,sK3) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(resolution,[],[f51,f45])).
% 1.50/0.57  fof(f1125,plain,(
% 1.50/0.57    ~r2_hidden(sK1,k2_xboole_0(sK2,sK3)) | ~v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f1122,f487])).
% 1.50/0.57  fof(f487,plain,(
% 1.50/0.57    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.50/0.57    inference(subsumption_resolution,[],[f486,f40])).
% 1.50/0.57  fof(f486,plain,(
% 1.50/0.57    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f485,f41])).
% 1.50/0.57  fof(f485,plain,(
% 1.50/0.57    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f484,f42])).
% 1.50/0.57  fof(f484,plain,(
% 1.50/0.57    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f483,f43])).
% 1.50/0.57  fof(f483,plain,(
% 1.50/0.57    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f477,f45])).
% 1.50/0.57  fof(f477,plain,(
% 1.50/0.57    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(superposition,[],[f50,f119])).
% 1.50/0.57  fof(f1122,plain,(
% 1.50/0.57    ~r2_hidden(sK1,k2_xboole_0(sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.50/0.57    inference(resolution,[],[f1121,f58])).
% 1.50/0.57  fof(f58,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f20])).
% 1.50/0.57  fof(f20,plain,(
% 1.50/0.57    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.50/0.57    inference(flattening,[],[f19])).
% 1.50/0.57  fof(f19,plain,(
% 1.50/0.57    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.50/0.57    inference(ennf_transformation,[],[f7])).
% 1.50/0.57  fof(f7,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_xboole_0(X1,X2),X0))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_tops_1)).
% 1.50/0.57  fof(f1121,plain,(
% 1.50/0.57    ~v3_pre_topc(k2_xboole_0(sK2,sK3),sK0) | ~r2_hidden(sK1,k2_xboole_0(sK2,sK3))),
% 1.50/0.57    inference(subsumption_resolution,[],[f1120,f490])).
% 1.50/0.57  fof(f490,plain,(
% 1.50/0.57    r1_tarski(sK2,u1_struct_0(sK0))),
% 1.50/0.57    inference(resolution,[],[f482,f56])).
% 1.50/0.57  fof(f56,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f34])).
% 1.50/0.57  fof(f34,plain,(
% 1.50/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.50/0.57    inference(nnf_transformation,[],[f5])).
% 1.50/0.57  fof(f5,axiom,(
% 1.50/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.50/0.57  fof(f1120,plain,(
% 1.50/0.57    ~v3_pre_topc(k2_xboole_0(sK2,sK3),sK0) | ~r2_hidden(sK1,k2_xboole_0(sK2,sK3)) | ~r1_tarski(sK2,u1_struct_0(sK0))),
% 1.50/0.57    inference(subsumption_resolution,[],[f1116,f495])).
% 1.50/0.57  fof(f495,plain,(
% 1.50/0.57    r1_tarski(sK3,u1_struct_0(sK0))),
% 1.50/0.57    inference(resolution,[],[f487,f56])).
% 1.50/0.57  fof(f1116,plain,(
% 1.50/0.57    ~v3_pre_topc(k2_xboole_0(sK2,sK3),sK0) | ~r2_hidden(sK1,k2_xboole_0(sK2,sK3)) | ~r1_tarski(sK3,u1_struct_0(sK0)) | ~r1_tarski(sK2,u1_struct_0(sK0))),
% 1.50/0.57    inference(resolution,[],[f1111,f59])).
% 1.50/0.57  fof(f59,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f22])).
% 1.50/0.57  fof(f22,plain,(
% 1.50/0.57    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.50/0.57    inference(flattening,[],[f21])).
% 1.50/0.57  fof(f21,plain,(
% 1.50/0.57    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.50/0.57    inference(ennf_transformation,[],[f3])).
% 1.50/0.57  fof(f3,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.50/0.57  fof(f1111,plain,(
% 1.50/0.57    ~r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0)) | ~v3_pre_topc(k2_xboole_0(sK2,sK3),sK0) | ~r2_hidden(sK1,k2_xboole_0(sK2,sK3))),
% 1.50/0.57    inference(resolution,[],[f879,f57])).
% 1.50/0.57  fof(f57,plain,(
% 1.50/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f34])).
% 1.50/0.57  fof(f879,plain,(
% 1.50/0.57    ~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k2_xboole_0(sK2,sK3)) | ~v3_pre_topc(k2_xboole_0(sK2,sK3),sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f878,f40])).
% 1.50/0.57  fof(f878,plain,(
% 1.50/0.57    ~v3_pre_topc(k2_xboole_0(sK2,sK3),sK0) | ~r2_hidden(sK1,k2_xboole_0(sK2,sK3)) | ~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f877,f41])).
% 1.50/0.57  fof(f877,plain,(
% 1.50/0.57    ~v3_pre_topc(k2_xboole_0(sK2,sK3),sK0) | ~r2_hidden(sK1,k2_xboole_0(sK2,sK3)) | ~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f876,f42])).
% 1.50/0.57  fof(f876,plain,(
% 1.50/0.57    ~v3_pre_topc(k2_xboole_0(sK2,sK3),sK0) | ~r2_hidden(sK1,k2_xboole_0(sK2,sK3)) | ~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(subsumption_resolution,[],[f869,f43])).
% 1.50/0.57  fof(f869,plain,(
% 1.50/0.57    ~v3_pre_topc(k2_xboole_0(sK2,sK3),sK0) | ~r2_hidden(sK1,k2_xboole_0(sK2,sK3)) | ~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.50/0.57    inference(resolution,[],[f49,f186])).
% 1.50/0.57  fof(f186,plain,(
% 1.50/0.57    ~r2_hidden(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.50/0.57    inference(resolution,[],[f168,f74])).
% 1.50/0.57  fof(f74,plain,(
% 1.50/0.57    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~r2_hidden(k2_xboole_0(sK2,sK3),X0)) )),
% 1.50/0.57    inference(resolution,[],[f73,f46])).
% 1.50/0.57  fof(f46,plain,(
% 1.50/0.57    ~m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.50/0.57    inference(cnf_transformation,[],[f29])).
% 1.50/0.57  fof(f73,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X2) | ~r1_tarski(X2,X1)) )),
% 1.50/0.57    inference(resolution,[],[f60,f57])).
% 1.50/0.57  fof(f60,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f24])).
% 1.50/0.57  fof(f24,plain,(
% 1.50/0.57    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.50/0.57    inference(flattening,[],[f23])).
% 1.50/0.57  fof(f23,plain,(
% 1.50/0.57    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.50/0.57    inference(ennf_transformation,[],[f6])).
% 1.50/0.57  fof(f6,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.50/0.57  fof(f168,plain,(
% 1.50/0.57    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.50/0.57    inference(superposition,[],[f54,f167])).
% 1.50/0.57  fof(f167,plain,(
% 1.50/0.57    ( ! [X21] : (k2_xboole_0(X21,X21) = X21) )),
% 1.50/0.57    inference(subsumption_resolution,[],[f166,f156])).
% 1.50/0.57  fof(f156,plain,(
% 1.50/0.57    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1) )),
% 1.50/0.57    inference(subsumption_resolution,[],[f152,f66])).
% 1.50/0.57  fof(f66,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),X2) | ~r2_hidden(sK5(X0,X1,X2),X1) | k2_xboole_0(X0,X1) = X2) )),
% 1.50/0.57    inference(cnf_transformation,[],[f39])).
% 1.50/0.57  fof(f152,plain,(
% 1.50/0.57    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1,X1),X1) | r2_hidden(sK5(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1) )),
% 1.50/0.57    inference(factoring,[],[f64])).
% 1.50/0.57  fof(f64,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | k2_xboole_0(X0,X1) = X2) )),
% 1.50/0.57    inference(cnf_transformation,[],[f39])).
% 1.50/0.57  fof(f166,plain,(
% 1.50/0.57    ( ! [X21] : (k2_xboole_0(X21,X21) = X21 | ~r2_hidden(sK5(X21,X21,X21),X21)) )),
% 1.50/0.57    inference(duplicate_literal_removal,[],[f163])).
% 1.50/0.57  fof(f163,plain,(
% 1.50/0.57    ( ! [X21] : (k2_xboole_0(X21,X21) = X21 | ~r2_hidden(sK5(X21,X21,X21),X21) | k2_xboole_0(X21,X21) = X21) )),
% 1.50/0.57    inference(resolution,[],[f156,f66])).
% 1.50/0.57  fof(f54,plain,(
% 1.50/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f2])).
% 1.50/0.57  fof(f2,axiom,(
% 1.50/0.57    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.50/0.57  fof(f49,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f31])).
% 1.50/0.57  fof(f31,plain,(
% 1.50/0.57    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.50/0.57    inference(flattening,[],[f30])).
% 1.50/0.57  fof(f30,plain,(
% 1.50/0.57    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.50/0.57    inference(nnf_transformation,[],[f15])).
% 1.50/0.57  fof(f15,plain,(
% 1.50/0.57    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.50/0.57    inference(flattening,[],[f14])).
% 1.50/0.57  fof(f14,plain,(
% 1.50/0.57    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.50/0.57    inference(ennf_transformation,[],[f9])).
% 1.50/0.57  fof(f9,axiom,(
% 1.50/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 1.50/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).
% 1.50/0.57  % SZS output end Proof for theBenchmark
% 1.50/0.57  % (6542)------------------------------
% 1.50/0.57  % (6542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (6542)Termination reason: Refutation
% 1.50/0.57  
% 1.50/0.57  % (6542)Memory used [KB]: 2302
% 1.50/0.57  % (6542)Time elapsed: 0.140 s
% 1.50/0.57  % (6542)------------------------------
% 1.50/0.57  % (6542)------------------------------
% 1.50/0.57  % (6523)Success in time 0.199 s
%------------------------------------------------------------------------------
