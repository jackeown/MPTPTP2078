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
% DateTime   : Thu Dec  3 13:11:16 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :  113 (1457 expanded)
%              Number of leaves         :   16 ( 427 expanded)
%              Depth                    :   24
%              Number of atoms          :  424 (14424 expanded)
%              Number of equality atoms :   26 (  31 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1570,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1556,f1314])).

fof(f1314,plain,(
    r1_tarski(sK3,k1_tops_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f1310,f230])).

fof(f230,plain,(
    r1_tarski(sK3,sK2) ),
    inference(resolution,[],[f189,f55])).

fof(f55,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | r1_tarski(sK3,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(sK1,X3)
          | ~ r1_tarski(X3,sK2)
          | ~ v3_pre_topc(X3,sK0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) )
    & ( ( r2_hidden(sK1,sK3)
        & r1_tarski(sK3,sK2)
        & v3_pre_topc(sK3,sK0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f43,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
            & ( ? [X4] :
                  ( r2_hidden(X1,X4)
                  & r1_tarski(X4,X2)
                  & v3_pre_topc(X4,X0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X1,k1_tops_1(X0,X2)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X2,X1] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,sK0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ r2_hidden(X1,k1_tops_1(sK0,X2)) )
          & ( ? [X4] :
                ( r2_hidden(X1,X4)
                & r1_tarski(X4,X2)
                & v3_pre_topc(X4,sK0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
            | r2_hidden(X1,k1_tops_1(sK0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X2,X1] :
        ( ( ! [X3] :
              ( ~ r2_hidden(X1,X3)
              | ~ r1_tarski(X3,X2)
              | ~ v3_pre_topc(X3,sK0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ r2_hidden(X1,k1_tops_1(sK0,X2)) )
        & ( ? [X4] :
              ( r2_hidden(X1,X4)
              & r1_tarski(X4,X2)
              & v3_pre_topc(X4,sK0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
          | r2_hidden(X1,k1_tops_1(sK0,X2)) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ! [X3] :
            ( ~ r2_hidden(sK1,X3)
            | ~ r1_tarski(X3,sK2)
            | ~ v3_pre_topc(X3,sK0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) )
      & ( ? [X4] :
            ( r2_hidden(sK1,X4)
            & r1_tarski(X4,sK2)
            & v3_pre_topc(X4,sK0)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
        | r2_hidden(sK1,k1_tops_1(sK0,sK2)) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X4] :
        ( r2_hidden(sK1,X4)
        & r1_tarski(X4,sK2)
        & v3_pre_topc(X4,sK0)
        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( r2_hidden(sK1,sK3)
      & r1_tarski(sK3,sK2)
      & v3_pre_topc(sK3,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
          & ( ? [X4] :
                ( r2_hidden(X1,X4)
                & r1_tarski(X4,X2)
                & v3_pre_topc(X4,X0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X1,k1_tops_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
          & ( ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X1,k1_tops_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
          & ( ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X1,k1_tops_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <~> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <~> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_hidden(X1,k1_tops_1(X0,X2))
            <=> ? [X3] :
                  ( r2_hidden(X1,X3)
                  & r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).

fof(f189,plain,(
    ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f188,f118])).

fof(f118,plain,(
    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f117,f50])).

fof(f50,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f117,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f102,f51])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f102,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f52,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f188,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f187,f108])).

fof(f108,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f94,f51])).

fof(f94,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f52,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f187,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f119,f57])).

fof(f57,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X3,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ r2_hidden(sK1,X3)
      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f119,plain,(
    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f103,f51])).

fof(f103,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f52,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f1310,plain,
    ( ~ r1_tarski(sK3,sK2)
    | r1_tarski(sK3,k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f1243,f52])).

fof(f1243,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK3,X0)
      | r1_tarski(sK3,k1_tops_1(sK0,X0)) ) ),
    inference(backward_demodulation,[],[f598,f1219])).

fof(f1219,plain,(
    sK3 = k1_tops_1(sK0,sK3) ),
    inference(resolution,[],[f1195,f309])).

fof(f309,plain,
    ( ~ r1_tarski(sK3,k1_tops_1(sK0,sK3))
    | sK3 = k1_tops_1(sK0,sK3) ),
    inference(resolution,[],[f298,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f298,plain,(
    r1_tarski(k1_tops_1(sK0,sK3),sK3) ),
    inference(subsumption_resolution,[],[f144,f189])).

fof(f144,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | r1_tarski(k1_tops_1(sK0,sK3),sK3) ),
    inference(subsumption_resolution,[],[f130,f51])).

fof(f130,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | r1_tarski(k1_tops_1(sK0,sK3),sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f53,f58])).

fof(f53,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f1195,plain,(
    r1_tarski(sK3,k1_tops_1(sK0,sK3)) ),
    inference(backward_demodulation,[],[f644,f1183])).

fof(f1183,plain,(
    k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) ),
    inference(backward_demodulation,[],[f566,f454])).

fof(f454,plain,(
    k3_subset_1(u1_struct_0(sK0),sK3) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) ),
    inference(subsumption_resolution,[],[f436,f321])).

fof(f321,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0) ),
    inference(subsumption_resolution,[],[f150,f189])).

fof(f150,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0) ),
    inference(subsumption_resolution,[],[f149,f54])).

fof(f54,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | v3_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f149,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0)
    | ~ v3_pre_topc(sK3,sK0) ),
    inference(subsumption_resolution,[],[f134,f51])).

fof(f134,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0)
    | ~ v3_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f53,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

fof(f436,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0)
    | k3_subset_1(u1_struct_0(sK0),sK3) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) ),
    inference(resolution,[],[f435,f85])).

fof(f85,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X2,sK0)
      | k2_pre_topc(sK0,X2) = X2 ) ),
    inference(resolution,[],[f51,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f435,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f143,f189])).

fof(f143,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f53,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f566,plain,(
    k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) ),
    inference(subsumption_resolution,[],[f145,f189])).

fof(f145,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) ),
    inference(subsumption_resolution,[],[f131,f51])).

fof(f131,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f53,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f644,plain,(
    r1_tarski(sK3,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3))) ),
    inference(subsumption_resolution,[],[f636,f435])).

fof(f636,plain,
    ( r1_tarski(sK3,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f634,f80])).

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f634,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k3_subset_1(u1_struct_0(sK0),sK3))
      | r1_tarski(sK3,k3_subset_1(u1_struct_0(sK0),X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f142,f189])).

fof(f142,plain,(
    ! [X3] :
      ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
      | r1_tarski(sK3,k3_subset_1(u1_struct_0(sK0),X3))
      | ~ r1_tarski(X3,k3_subset_1(u1_struct_0(sK0),sK3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f53,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

fof(f598,plain,(
    ! [X0] :
      ( r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X0))
      | ~ r1_tarski(sK3,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f151,f189])).

fof(f151,plain,(
    ! [X0] :
      ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
      | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X0))
      | ~ r1_tarski(sK3,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f136,f51])).

fof(f136,plain,(
    ! [X0] :
      ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
      | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X0))
      | ~ r1_tarski(sK3,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f53,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f1556,plain,(
    ~ r1_tarski(sK3,k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f306,f232])).

fof(f232,plain,(
    ~ r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f189,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f306,plain,(
    ! [X2] :
      ( r1_tarski(k1_tarski(sK1),X2)
      | ~ r1_tarski(sK3,X2) ) ),
    inference(resolution,[],[f240,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f240,plain,(
    r1_tarski(k1_tarski(sK1),sK3) ),
    inference(resolution,[],[f229,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f229,plain,(
    r2_hidden(sK1,sK3) ),
    inference(resolution,[],[f189,f56])).

fof(f56,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n024.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 10:05:21 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.22/0.49  % (2143)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.50  % (2159)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.51  % (2148)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (2135)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (2139)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  % (2142)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (2151)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.53  % (2156)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.53  % (2136)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (2137)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.53  % (2140)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (2138)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.53  % (2153)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.54  % (2157)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.54  % (2149)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.54  % (2144)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.54  % (2145)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.55  % (2147)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.55  % (2141)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.55  % (2160)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.55  % (2146)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.55  % (2154)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.56  % (2150)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.56  % (2155)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.57  % (2152)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.57  % (2158)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.63/0.60  % (2153)Refutation found. Thanks to Tanya!
% 1.63/0.60  % SZS status Theorem for theBenchmark
% 1.63/0.60  % SZS output start Proof for theBenchmark
% 1.63/0.60  fof(f1570,plain,(
% 1.63/0.60    $false),
% 1.63/0.60    inference(subsumption_resolution,[],[f1556,f1314])).
% 1.63/0.60  fof(f1314,plain,(
% 1.63/0.60    r1_tarski(sK3,k1_tops_1(sK0,sK2))),
% 1.63/0.60    inference(subsumption_resolution,[],[f1310,f230])).
% 1.63/0.60  fof(f230,plain,(
% 1.63/0.60    r1_tarski(sK3,sK2)),
% 1.63/0.60    inference(resolution,[],[f189,f55])).
% 1.63/0.60  fof(f55,plain,(
% 1.63/0.60    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | r1_tarski(sK3,sK2)),
% 1.63/0.60    inference(cnf_transformation,[],[f44])).
% 1.63/0.60  fof(f44,plain,(
% 1.63/0.60    ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) & ((r2_hidden(sK1,sK3) & r1_tarski(sK3,sK2) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.63/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f43,f42,f41])).
% 1.63/0.60  fof(f41,plain,(
% 1.63/0.60    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X2,X1] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X1,k1_tops_1(sK0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(X1,k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.63/0.60    introduced(choice_axiom,[])).
% 1.63/0.60  fof(f42,plain,(
% 1.63/0.60    ? [X2,X1] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X1,k1_tops_1(sK0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(X1,k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) & (? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,sK2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.63/0.60    introduced(choice_axiom,[])).
% 1.63/0.60  fof(f43,plain,(
% 1.63/0.60    ? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,sK2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) => (r2_hidden(sK1,sK3) & r1_tarski(sK3,sK2) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.63/0.60    introduced(choice_axiom,[])).
% 1.63/0.60  fof(f40,plain,(
% 1.63/0.60    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.63/0.60    inference(rectify,[],[f39])).
% 1.63/0.60  fof(f39,plain,(
% 1.63/0.60    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.63/0.60    inference(flattening,[],[f38])).
% 1.63/0.60  fof(f38,plain,(
% 1.63/0.60    ? [X0] : (? [X1,X2] : (((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.63/0.60    inference(nnf_transformation,[],[f19])).
% 1.63/0.60  fof(f19,plain,(
% 1.63/0.60    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.63/0.60    inference(flattening,[],[f18])).
% 1.63/0.60  fof(f18,plain,(
% 1.63/0.60    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.63/0.60    inference(ennf_transformation,[],[f17])).
% 1.63/0.60  fof(f17,negated_conjecture,(
% 1.63/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 1.63/0.60    inference(negated_conjecture,[],[f16])).
% 1.63/0.60  fof(f16,conjecture,(
% 1.63/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).
% 1.63/0.60  fof(f189,plain,(
% 1.63/0.60    ~r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 1.63/0.60    inference(subsumption_resolution,[],[f188,f118])).
% 1.63/0.60  fof(f118,plain,(
% 1.63/0.60    v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 1.63/0.60    inference(subsumption_resolution,[],[f117,f50])).
% 1.63/0.60  fof(f50,plain,(
% 1.63/0.60    v2_pre_topc(sK0)),
% 1.63/0.60    inference(cnf_transformation,[],[f44])).
% 1.63/0.60  fof(f117,plain,(
% 1.63/0.60    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~v2_pre_topc(sK0)),
% 1.63/0.60    inference(subsumption_resolution,[],[f102,f51])).
% 1.63/0.60  fof(f51,plain,(
% 1.63/0.60    l1_pre_topc(sK0)),
% 1.63/0.60    inference(cnf_transformation,[],[f44])).
% 1.63/0.60  fof(f102,plain,(
% 1.63/0.60    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.63/0.60    inference(resolution,[],[f52,f68])).
% 1.63/0.60  fof(f68,plain,(
% 1.63/0.60    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f32])).
% 1.63/0.60  fof(f32,plain,(
% 1.63/0.60    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.63/0.60    inference(flattening,[],[f31])).
% 1.63/0.60  fof(f31,plain,(
% 1.63/0.60    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.63/0.60    inference(ennf_transformation,[],[f12])).
% 1.63/0.60  fof(f12,axiom,(
% 1.63/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 1.63/0.60  fof(f52,plain,(
% 1.63/0.60    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.63/0.60    inference(cnf_transformation,[],[f44])).
% 1.63/0.60  fof(f188,plain,(
% 1.63/0.60    ~v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 1.63/0.60    inference(subsumption_resolution,[],[f187,f108])).
% 1.63/0.60  fof(f108,plain,(
% 1.63/0.60    r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 1.63/0.60    inference(subsumption_resolution,[],[f94,f51])).
% 1.63/0.60  fof(f94,plain,(
% 1.63/0.60    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~l1_pre_topc(sK0)),
% 1.63/0.60    inference(resolution,[],[f52,f58])).
% 1.63/0.60  fof(f58,plain,(
% 1.63/0.60    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f20])).
% 1.63/0.60  fof(f20,plain,(
% 1.63/0.60    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.63/0.60    inference(ennf_transformation,[],[f14])).
% 1.63/0.60  fof(f14,axiom,(
% 1.63/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 1.63/0.60  fof(f187,plain,(
% 1.63/0.60    ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 1.63/0.60    inference(duplicate_literal_removal,[],[f172])).
% 1.63/0.60  fof(f172,plain,(
% 1.63/0.60    ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 1.63/0.60    inference(resolution,[],[f119,f57])).
% 1.63/0.60  fof(f57,plain,(
% 1.63/0.60    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) )),
% 1.63/0.60    inference(cnf_transformation,[],[f44])).
% 1.63/0.60  fof(f119,plain,(
% 1.63/0.60    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.63/0.60    inference(subsumption_resolution,[],[f103,f51])).
% 1.63/0.60  fof(f103,plain,(
% 1.63/0.60    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.63/0.60    inference(resolution,[],[f52,f69])).
% 1.63/0.60  fof(f69,plain,(
% 1.63/0.60    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f34])).
% 1.63/0.60  fof(f34,plain,(
% 1.63/0.60    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.63/0.60    inference(flattening,[],[f33])).
% 1.63/0.60  fof(f33,plain,(
% 1.63/0.60    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.63/0.60    inference(ennf_transformation,[],[f11])).
% 1.63/0.60  fof(f11,axiom,(
% 1.63/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 1.63/0.60  fof(f1310,plain,(
% 1.63/0.60    ~r1_tarski(sK3,sK2) | r1_tarski(sK3,k1_tops_1(sK0,sK2))),
% 1.63/0.60    inference(resolution,[],[f1243,f52])).
% 1.63/0.60  fof(f1243,plain,(
% 1.63/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK3,X0) | r1_tarski(sK3,k1_tops_1(sK0,X0))) )),
% 1.63/0.60    inference(backward_demodulation,[],[f598,f1219])).
% 1.63/0.60  fof(f1219,plain,(
% 1.63/0.60    sK3 = k1_tops_1(sK0,sK3)),
% 1.63/0.60    inference(resolution,[],[f1195,f309])).
% 1.63/0.60  fof(f309,plain,(
% 1.63/0.60    ~r1_tarski(sK3,k1_tops_1(sK0,sK3)) | sK3 = k1_tops_1(sK0,sK3)),
% 1.63/0.60    inference(resolution,[],[f298,f72])).
% 1.63/0.60  fof(f72,plain,(
% 1.63/0.60    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f47])).
% 1.63/0.60  fof(f47,plain,(
% 1.63/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.63/0.60    inference(flattening,[],[f46])).
% 1.63/0.60  fof(f46,plain,(
% 1.63/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.63/0.60    inference(nnf_transformation,[],[f1])).
% 1.63/0.60  fof(f1,axiom,(
% 1.63/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.63/0.60  fof(f298,plain,(
% 1.63/0.60    r1_tarski(k1_tops_1(sK0,sK3),sK3)),
% 1.63/0.60    inference(subsumption_resolution,[],[f144,f189])).
% 1.63/0.60  fof(f144,plain,(
% 1.63/0.60    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | r1_tarski(k1_tops_1(sK0,sK3),sK3)),
% 1.63/0.60    inference(subsumption_resolution,[],[f130,f51])).
% 1.63/0.60  fof(f130,plain,(
% 1.63/0.60    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | r1_tarski(k1_tops_1(sK0,sK3),sK3) | ~l1_pre_topc(sK0)),
% 1.63/0.60    inference(resolution,[],[f53,f58])).
% 1.63/0.60  fof(f53,plain,(
% 1.63/0.60    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 1.63/0.60    inference(cnf_transformation,[],[f44])).
% 1.63/0.60  fof(f1195,plain,(
% 1.63/0.60    r1_tarski(sK3,k1_tops_1(sK0,sK3))),
% 1.63/0.60    inference(backward_demodulation,[],[f644,f1183])).
% 1.63/0.60  fof(f1183,plain,(
% 1.63/0.60    k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3))),
% 1.63/0.60    inference(backward_demodulation,[],[f566,f454])).
% 1.63/0.60  fof(f454,plain,(
% 1.63/0.60    k3_subset_1(u1_struct_0(sK0),sK3) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))),
% 1.63/0.60    inference(subsumption_resolution,[],[f436,f321])).
% 1.63/0.60  fof(f321,plain,(
% 1.63/0.60    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0)),
% 1.63/0.60    inference(subsumption_resolution,[],[f150,f189])).
% 1.63/0.60  fof(f150,plain,(
% 1.63/0.60    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0)),
% 1.63/0.60    inference(subsumption_resolution,[],[f149,f54])).
% 1.63/0.60  fof(f54,plain,(
% 1.63/0.60    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | v3_pre_topc(sK3,sK0)),
% 1.63/0.60    inference(cnf_transformation,[],[f44])).
% 1.63/0.60  fof(f149,plain,(
% 1.63/0.60    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0) | ~v3_pre_topc(sK3,sK0)),
% 1.63/0.60    inference(subsumption_resolution,[],[f134,f51])).
% 1.63/0.60  fof(f134,plain,(
% 1.63/0.60    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0) | ~v3_pre_topc(sK3,sK0) | ~l1_pre_topc(sK0)),
% 1.63/0.60    inference(resolution,[],[f53,f62])).
% 1.79/0.62  fof(f62,plain,(
% 1.79/0.62    ( ! [X0,X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f45])).
% 1.79/0.62  fof(f45,plain,(
% 1.79/0.62    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.62    inference(nnf_transformation,[],[f24])).
% 1.79/0.62  fof(f24,plain,(
% 1.79/0.62    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.62    inference(ennf_transformation,[],[f13])).
% 1.79/0.62  fof(f13,axiom,(
% 1.79/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).
% 1.79/0.62  fof(f436,plain,(
% 1.79/0.62    ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0) | k3_subset_1(u1_struct_0(sK0),sK3) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))),
% 1.79/0.62    inference(resolution,[],[f435,f85])).
% 1.79/0.62  fof(f85,plain,(
% 1.79/0.62    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X2,sK0) | k2_pre_topc(sK0,X2) = X2) )),
% 1.79/0.62    inference(resolution,[],[f51,f60])).
% 1.79/0.62  fof(f60,plain,(
% 1.79/0.62    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f23])).
% 1.79/0.62  fof(f23,plain,(
% 1.79/0.62    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.62    inference(flattening,[],[f22])).
% 1.79/0.62  fof(f22,plain,(
% 1.79/0.62    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.62    inference(ennf_transformation,[],[f9])).
% 1.79/0.62  fof(f9,axiom,(
% 1.79/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.79/0.62  fof(f435,plain,(
% 1.79/0.62    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.79/0.62    inference(subsumption_resolution,[],[f143,f189])).
% 1.79/0.62  fof(f143,plain,(
% 1.79/0.62    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.79/0.62    inference(resolution,[],[f53,f66])).
% 1.79/0.62  fof(f66,plain,(
% 1.79/0.62    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.79/0.62    inference(cnf_transformation,[],[f28])).
% 1.79/0.62  fof(f28,plain,(
% 1.79/0.62    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.79/0.62    inference(ennf_transformation,[],[f6])).
% 1.79/0.62  fof(f6,axiom,(
% 1.79/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.79/0.62  fof(f566,plain,(
% 1.79/0.62    k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)))),
% 1.79/0.62    inference(subsumption_resolution,[],[f145,f189])).
% 1.79/0.62  fof(f145,plain,(
% 1.79/0.62    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)))),
% 1.79/0.62    inference(subsumption_resolution,[],[f131,f51])).
% 1.79/0.62  fof(f131,plain,(
% 1.79/0.62    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) | ~l1_pre_topc(sK0)),
% 1.79/0.62    inference(resolution,[],[f53,f59])).
% 1.79/0.62  fof(f59,plain,(
% 1.79/0.62    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f21])).
% 1.79/0.62  fof(f21,plain,(
% 1.79/0.62    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.62    inference(ennf_transformation,[],[f10])).
% 1.79/0.62  fof(f10,axiom,(
% 1.79/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 1.79/0.62  fof(f644,plain,(
% 1.79/0.62    r1_tarski(sK3,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)))),
% 1.79/0.62    inference(subsumption_resolution,[],[f636,f435])).
% 1.79/0.62  fof(f636,plain,(
% 1.79/0.62    r1_tarski(sK3,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3))) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.79/0.62    inference(resolution,[],[f634,f80])).
% 1.79/0.62  fof(f80,plain,(
% 1.79/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.79/0.62    inference(equality_resolution,[],[f70])).
% 1.79/0.62  fof(f70,plain,(
% 1.79/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.79/0.62    inference(cnf_transformation,[],[f47])).
% 1.79/0.62  fof(f634,plain,(
% 1.79/0.62    ( ! [X3] : (~r1_tarski(X3,k3_subset_1(u1_struct_0(sK0),sK3)) | r1_tarski(sK3,k3_subset_1(u1_struct_0(sK0),X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.79/0.62    inference(subsumption_resolution,[],[f142,f189])).
% 1.79/0.62  fof(f142,plain,(
% 1.79/0.62    ( ! [X3] : (r2_hidden(sK1,k1_tops_1(sK0,sK2)) | r1_tarski(sK3,k3_subset_1(u1_struct_0(sK0),X3)) | ~r1_tarski(X3,k3_subset_1(u1_struct_0(sK0),sK3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.79/0.62    inference(resolution,[],[f53,f67])).
% 1.79/0.62  fof(f67,plain,(
% 1.79/0.62    ( ! [X2,X0,X1] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.79/0.62    inference(cnf_transformation,[],[f30])).
% 1.79/0.62  fof(f30,plain,(
% 1.79/0.62    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.79/0.62    inference(flattening,[],[f29])).
% 1.79/0.62  fof(f29,plain,(
% 1.79/0.62    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.79/0.62    inference(ennf_transformation,[],[f7])).
% 1.79/0.62  fof(f7,axiom,(
% 1.79/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).
% 1.79/0.62  fof(f598,plain,(
% 1.79/0.62    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X0)) | ~r1_tarski(sK3,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.79/0.62    inference(subsumption_resolution,[],[f151,f189])).
% 1.79/0.62  fof(f151,plain,(
% 1.79/0.62    ( ! [X0] : (r2_hidden(sK1,k1_tops_1(sK0,sK2)) | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X0)) | ~r1_tarski(sK3,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.79/0.62    inference(subsumption_resolution,[],[f136,f51])).
% 1.79/0.62  fof(f136,plain,(
% 1.79/0.62    ( ! [X0] : (r2_hidden(sK1,k1_tops_1(sK0,sK2)) | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X0)) | ~r1_tarski(sK3,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.79/0.62    inference(resolution,[],[f53,f64])).
% 1.79/0.62  fof(f64,plain,(
% 1.79/0.62    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f26])).
% 1.79/0.62  fof(f26,plain,(
% 1.79/0.62    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.62    inference(flattening,[],[f25])).
% 1.79/0.62  fof(f25,plain,(
% 1.79/0.62    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.62    inference(ennf_transformation,[],[f15])).
% 1.79/0.62  fof(f15,axiom,(
% 1.79/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 1.79/0.62  fof(f1556,plain,(
% 1.79/0.62    ~r1_tarski(sK3,k1_tops_1(sK0,sK2))),
% 1.79/0.62    inference(resolution,[],[f306,f232])).
% 1.79/0.62  fof(f232,plain,(
% 1.79/0.62    ~r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2))),
% 1.79/0.62    inference(resolution,[],[f189,f75])).
% 1.79/0.62  fof(f75,plain,(
% 1.79/0.62    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f49])).
% 1.79/0.62  fof(f49,plain,(
% 1.79/0.62    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.79/0.62    inference(nnf_transformation,[],[f5])).
% 1.79/0.62  fof(f5,axiom,(
% 1.79/0.62    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.79/0.62  fof(f306,plain,(
% 1.79/0.62    ( ! [X2] : (r1_tarski(k1_tarski(sK1),X2) | ~r1_tarski(sK3,X2)) )),
% 1.79/0.62    inference(resolution,[],[f240,f78])).
% 1.79/0.62  fof(f78,plain,(
% 1.79/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f37])).
% 1.79/0.62  fof(f37,plain,(
% 1.79/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.79/0.62    inference(flattening,[],[f36])).
% 1.79/0.62  fof(f36,plain,(
% 1.79/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.79/0.62    inference(ennf_transformation,[],[f4])).
% 1.79/0.62  fof(f4,axiom,(
% 1.79/0.62    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.79/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.79/0.62  fof(f240,plain,(
% 1.79/0.62    r1_tarski(k1_tarski(sK1),sK3)),
% 1.79/0.62    inference(resolution,[],[f229,f76])).
% 1.79/0.62  fof(f76,plain,(
% 1.79/0.62    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f49])).
% 1.79/0.62  fof(f229,plain,(
% 1.79/0.62    r2_hidden(sK1,sK3)),
% 1.79/0.62    inference(resolution,[],[f189,f56])).
% 1.79/0.62  fof(f56,plain,(
% 1.79/0.62    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | r2_hidden(sK1,sK3)),
% 1.79/0.62    inference(cnf_transformation,[],[f44])).
% 1.79/0.62  % SZS output end Proof for theBenchmark
% 1.79/0.62  % (2153)------------------------------
% 1.79/0.62  % (2153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.62  % (2153)Termination reason: Refutation
% 1.79/0.62  
% 1.79/0.62  % (2153)Memory used [KB]: 2046
% 1.79/0.62  % (2153)Time elapsed: 0.178 s
% 1.79/0.62  % (2153)------------------------------
% 1.79/0.62  % (2153)------------------------------
% 1.79/0.63  % (2134)Success in time 0.246 s
%------------------------------------------------------------------------------
