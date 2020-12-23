%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:27 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 178 expanded)
%              Number of leaves         :    9 (  63 expanded)
%              Depth                    :   16
%              Number of atoms          :  267 (1156 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75,plain,(
    $false ),
    inference(subsumption_resolution,[],[f74,f53])).

fof(f53,plain,(
    r2_hidden(sK3(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f52,f24])).

fof(f24,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ v1_tops_2(sK1,sK0)
    & v1_tops_2(sK2,sK0)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f13,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_2(X1,X0)
                & v1_tops_2(X2,X0)
                & r1_tarski(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(X1,sK0)
              & v1_tops_2(X2,sK0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tops_2(X1,sK0)
            & v1_tops_2(X2,sK0)
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X2] :
          ( ~ v1_tops_2(sK1,sK0)
          & v1_tops_2(X2,sK0)
          & r1_tarski(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X2] :
        ( ~ v1_tops_2(sK1,sK0)
        & v1_tops_2(X2,sK0)
        & r1_tarski(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ v1_tops_2(sK1,sK0)
      & v1_tops_2(sK2,sK0)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(X1,X0)
              & v1_tops_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(X1,X0)
              & v1_tops_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( ( v1_tops_2(X2,X0)
                    & r1_tarski(X1,X2) )
                 => v1_tops_2(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v1_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v1_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tops_2)).

fof(f52,plain,
    ( r2_hidden(sK3(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f50,f29])).

fof(f29,plain,(
    ~ v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,
    ( r2_hidden(sK3(sK0,sK1),sK1)
    | v1_tops_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f32,f25])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r2_hidden(sK3(X0,X1),X1)
      | v1_tops_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK3(X0,X1),X0)
                & r2_hidden(sK3(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK3(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).

fof(f74,plain,(
    ~ r2_hidden(sK3(sK0,sK1),sK1) ),
    inference(resolution,[],[f73,f46])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f45,f27])).

fof(f27,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1) ) ),
    inference(superposition,[],[f42,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f42,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & ~ r2_hidden(sK4(X0,X1,X2),X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & ~ r2_hidden(sK4(X0,X1,X2),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

% (20716)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% (20718)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% (20716)Refutation not found, incomplete strategy% (20716)------------------------------
% (20716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f19,plain,(
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

fof(f73,plain,(
    ~ r2_hidden(sK3(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f72,f29])).

fof(f72,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ r2_hidden(sK3(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f70,f57])).

fof(f57,plain,(
    ~ v3_pre_topc(sK3(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f56,f24])).

fof(f56,plain,
    ( ~ v3_pre_topc(sK3(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f54,f29])).

fof(f54,plain,
    ( ~ v3_pre_topc(sK3(sK0,sK1),sK0)
    | v1_tops_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f33,f25])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v3_pre_topc(sK3(X0,X1),X0)
      | v1_tops_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f70,plain,
    ( v3_pre_topc(sK3(sK0,sK1),sK0)
    | v1_tops_2(sK1,sK0)
    | ~ r2_hidden(sK3(sK0,sK1),sK2) ),
    inference(resolution,[],[f69,f25])).

fof(f69,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v3_pre_topc(sK3(sK0,X0),sK0)
      | v1_tops_2(X0,sK0)
      | ~ r2_hidden(sK3(sK0,X0),sK2) ) ),
    inference(subsumption_resolution,[],[f68,f24])).

fof(f68,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK0,X0),sK2)
      | v3_pre_topc(sK3(sK0,X0),sK0)
      | v1_tops_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f67,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,sK2)
      | v3_pre_topc(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f66,f24])).

fof(f66,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X1,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f65,f28])).

fof(f28,plain,(
    v1_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f65,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_tops_2(sK2,sK0)
      | v3_pre_topc(X1,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f30,f26])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | v3_pre_topc(X3,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:14:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.36  ipcrm: permission denied for id (814350336)
% 0.20/0.36  ipcrm: permission denied for id (814383106)
% 0.20/0.36  ipcrm: permission denied for id (816939012)
% 0.20/0.36  ipcrm: permission denied for id (816971781)
% 0.20/0.37  ipcrm: permission denied for id (819953671)
% 0.20/0.37  ipcrm: permission denied for id (814448649)
% 0.20/0.37  ipcrm: permission denied for id (814481419)
% 0.20/0.37  ipcrm: permission denied for id (814514188)
% 0.20/0.37  ipcrm: permission denied for id (814546957)
% 0.20/0.37  ipcrm: permission denied for id (820051982)
% 0.20/0.38  ipcrm: permission denied for id (817168399)
% 0.20/0.38  ipcrm: permission denied for id (814612496)
% 0.20/0.38  ipcrm: permission denied for id (817201169)
% 0.20/0.38  ipcrm: permission denied for id (814645266)
% 0.20/0.38  ipcrm: permission denied for id (814678035)
% 0.20/0.38  ipcrm: permission denied for id (817233940)
% 0.20/0.38  ipcrm: permission denied for id (820117526)
% 0.20/0.38  ipcrm: permission denied for id (817332247)
% 0.20/0.39  ipcrm: permission denied for id (820150296)
% 0.20/0.39  ipcrm: permission denied for id (814809113)
% 0.20/0.39  ipcrm: permission denied for id (817397786)
% 0.20/0.39  ipcrm: permission denied for id (814874651)
% 0.20/0.39  ipcrm: permission denied for id (817430556)
% 0.20/0.39  ipcrm: permission denied for id (817463325)
% 0.20/0.39  ipcrm: permission denied for id (820183070)
% 0.20/0.39  ipcrm: permission denied for id (815005728)
% 0.20/0.40  ipcrm: permission denied for id (815038497)
% 0.20/0.40  ipcrm: permission denied for id (820248610)
% 0.20/0.40  ipcrm: permission denied for id (817594403)
% 0.20/0.40  ipcrm: permission denied for id (817627172)
% 0.20/0.40  ipcrm: permission denied for id (817692710)
% 0.20/0.40  ipcrm: permission denied for id (820346920)
% 0.20/0.41  ipcrm: permission denied for id (817791017)
% 0.20/0.41  ipcrm: permission denied for id (815202346)
% 0.20/0.41  ipcrm: permission denied for id (820379691)
% 0.20/0.41  ipcrm: permission denied for id (815235116)
% 0.20/0.41  ipcrm: permission denied for id (817856557)
% 0.20/0.41  ipcrm: permission denied for id (820412462)
% 0.20/0.41  ipcrm: permission denied for id (815300655)
% 0.20/0.41  ipcrm: permission denied for id (817922096)
% 0.20/0.41  ipcrm: permission denied for id (817954865)
% 0.20/0.42  ipcrm: permission denied for id (820478003)
% 0.20/0.42  ipcrm: permission denied for id (815366196)
% 0.20/0.42  ipcrm: permission denied for id (818053173)
% 0.20/0.42  ipcrm: permission denied for id (818118711)
% 0.20/0.42  ipcrm: permission denied for id (820543544)
% 0.20/0.42  ipcrm: permission denied for id (818184249)
% 0.20/0.42  ipcrm: permission denied for id (820576314)
% 0.20/0.43  ipcrm: permission denied for id (818249787)
% 0.20/0.43  ipcrm: permission denied for id (818282556)
% 0.20/0.43  ipcrm: permission denied for id (815497277)
% 0.20/0.43  ipcrm: permission denied for id (815530046)
% 0.20/0.43  ipcrm: permission denied for id (820609087)
% 0.20/0.43  ipcrm: permission denied for id (815562816)
% 0.20/0.43  ipcrm: permission denied for id (815595585)
% 0.20/0.43  ipcrm: permission denied for id (820641858)
% 0.20/0.44  ipcrm: permission denied for id (820674627)
% 0.20/0.44  ipcrm: permission denied for id (818413636)
% 0.20/0.44  ipcrm: permission denied for id (818446405)
% 0.20/0.44  ipcrm: permission denied for id (818479174)
% 0.20/0.44  ipcrm: permission denied for id (815661127)
% 0.20/0.44  ipcrm: permission denied for id (818511944)
% 0.20/0.44  ipcrm: permission denied for id (815726665)
% 0.20/0.44  ipcrm: permission denied for id (815759434)
% 0.20/0.45  ipcrm: permission denied for id (820740172)
% 0.20/0.45  ipcrm: permission denied for id (815824973)
% 0.20/0.45  ipcrm: permission denied for id (820805711)
% 0.20/0.45  ipcrm: permission denied for id (818675792)
% 0.20/0.45  ipcrm: permission denied for id (815890514)
% 0.20/0.45  ipcrm: permission denied for id (820904020)
% 0.20/0.46  ipcrm: permission denied for id (818872407)
% 0.20/0.46  ipcrm: permission denied for id (821035097)
% 0.20/0.46  ipcrm: permission denied for id (815988826)
% 0.20/0.46  ipcrm: permission denied for id (819003483)
% 0.20/0.46  ipcrm: permission denied for id (819036252)
% 0.20/0.47  ipcrm: permission denied for id (816087133)
% 0.20/0.47  ipcrm: permission denied for id (821067870)
% 0.20/0.47  ipcrm: permission denied for id (819101791)
% 0.20/0.47  ipcrm: permission denied for id (816119904)
% 0.20/0.47  ipcrm: permission denied for id (819167330)
% 0.20/0.47  ipcrm: permission denied for id (819232867)
% 0.20/0.48  ipcrm: permission denied for id (819331174)
% 0.20/0.48  ipcrm: permission denied for id (819363943)
% 0.20/0.48  ipcrm: permission denied for id (816349289)
% 0.20/0.48  ipcrm: permission denied for id (816382058)
% 0.20/0.48  ipcrm: permission denied for id (821231723)
% 0.20/0.48  ipcrm: permission denied for id (819462252)
% 0.20/0.48  ipcrm: permission denied for id (819495021)
% 0.20/0.49  ipcrm: permission denied for id (821297263)
% 0.20/0.49  ipcrm: permission denied for id (819593328)
% 0.20/0.49  ipcrm: permission denied for id (819626097)
% 0.20/0.49  ipcrm: permission denied for id (816480370)
% 0.20/0.49  ipcrm: permission denied for id (819658867)
% 0.20/0.49  ipcrm: permission denied for id (816513140)
% 0.20/0.49  ipcrm: permission denied for id (821330037)
% 0.20/0.49  ipcrm: permission denied for id (819757175)
% 0.20/0.50  ipcrm: permission denied for id (819789944)
% 0.20/0.50  ipcrm: permission denied for id (816611449)
% 0.20/0.50  ipcrm: permission denied for id (816644218)
% 0.20/0.50  ipcrm: permission denied for id (816676987)
% 0.20/0.50  ipcrm: permission denied for id (816775293)
% 0.20/0.50  ipcrm: permission denied for id (816808062)
% 0.20/0.50  ipcrm: permission denied for id (816840831)
% 0.76/0.61  % (20725)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.76/0.61  % (20731)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.76/0.61  % (20722)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.76/0.62  % (20734)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.76/0.62  % (20734)Refutation found. Thanks to Tanya!
% 0.76/0.62  % SZS status Theorem for theBenchmark
% 0.76/0.62  % SZS output start Proof for theBenchmark
% 0.76/0.62  fof(f75,plain,(
% 0.76/0.62    $false),
% 0.76/0.62    inference(subsumption_resolution,[],[f74,f53])).
% 0.76/0.62  fof(f53,plain,(
% 0.76/0.62    r2_hidden(sK3(sK0,sK1),sK1)),
% 0.76/0.62    inference(subsumption_resolution,[],[f52,f24])).
% 0.76/0.62  fof(f24,plain,(
% 0.76/0.62    l1_pre_topc(sK0)),
% 0.76/0.62    inference(cnf_transformation,[],[f14])).
% 0.76/0.62  fof(f14,plain,(
% 0.76/0.62    ((~v1_tops_2(sK1,sK0) & v1_tops_2(sK2,sK0) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 0.76/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f13,f12,f11])).
% 0.76/0.62  fof(f11,plain,(
% 0.76/0.62    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(X1,X0) & v1_tops_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_2(X1,sK0) & v1_tops_2(X2,sK0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 0.76/0.62    introduced(choice_axiom,[])).
% 0.76/0.62  fof(f12,plain,(
% 0.76/0.62    ? [X1] : (? [X2] : (~v1_tops_2(X1,sK0) & v1_tops_2(X2,sK0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X2] : (~v1_tops_2(sK1,sK0) & v1_tops_2(X2,sK0) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.76/0.62    introduced(choice_axiom,[])).
% 0.76/0.62  fof(f13,plain,(
% 0.76/0.62    ? [X2] : (~v1_tops_2(sK1,sK0) & v1_tops_2(X2,sK0) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~v1_tops_2(sK1,sK0) & v1_tops_2(sK2,sK0) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.76/0.62    introduced(choice_axiom,[])).
% 0.76/0.62  fof(f7,plain,(
% 0.76/0.62    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(X1,X0) & v1_tops_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.76/0.62    inference(flattening,[],[f6])).
% 0.76/0.62  fof(f6,plain,(
% 0.76/0.62    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_2(X1,X0) & (v1_tops_2(X2,X0) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.76/0.62    inference(ennf_transformation,[],[f5])).
% 0.76/0.62  fof(f5,negated_conjecture,(
% 0.76/0.62    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & r1_tarski(X1,X2)) => v1_tops_2(X1,X0)))))),
% 0.76/0.62    inference(negated_conjecture,[],[f4])).
% 0.76/0.62  fof(f4,conjecture,(
% 0.76/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & r1_tarski(X1,X2)) => v1_tops_2(X1,X0)))))),
% 0.76/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tops_2)).
% 0.76/0.62  fof(f52,plain,(
% 0.76/0.62    r2_hidden(sK3(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 0.76/0.62    inference(subsumption_resolution,[],[f50,f29])).
% 0.76/0.62  fof(f29,plain,(
% 0.76/0.62    ~v1_tops_2(sK1,sK0)),
% 0.76/0.62    inference(cnf_transformation,[],[f14])).
% 0.76/0.62  fof(f50,plain,(
% 0.76/0.62    r2_hidden(sK3(sK0,sK1),sK1) | v1_tops_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.76/0.62    inference(resolution,[],[f32,f25])).
% 0.76/0.62  fof(f25,plain,(
% 0.76/0.62    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.76/0.62    inference(cnf_transformation,[],[f14])).
% 0.76/0.62  fof(f32,plain,(
% 0.76/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK3(X0,X1),X1) | v1_tops_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.76/0.62    inference(cnf_transformation,[],[f18])).
% 0.76/0.62  fof(f18,plain,(
% 0.76/0.62    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | (~v3_pre_topc(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.76/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).
% 0.76/0.62  fof(f17,plain,(
% 0.76/0.62    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.76/0.62    introduced(choice_axiom,[])).
% 0.76/0.62  fof(f16,plain,(
% 0.76/0.62    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.76/0.62    inference(rectify,[],[f15])).
% 0.76/0.62  fof(f15,plain,(
% 0.76/0.62    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.76/0.62    inference(nnf_transformation,[],[f9])).
% 0.76/0.62  fof(f9,plain,(
% 0.76/0.62    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.76/0.62    inference(flattening,[],[f8])).
% 0.76/0.62  fof(f8,plain,(
% 0.76/0.62    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.76/0.62    inference(ennf_transformation,[],[f3])).
% 0.76/0.62  fof(f3,axiom,(
% 0.76/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v3_pre_topc(X2,X0))))))),
% 0.76/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).
% 0.76/0.62  fof(f74,plain,(
% 0.76/0.62    ~r2_hidden(sK3(sK0,sK1),sK1)),
% 0.76/0.62    inference(resolution,[],[f73,f46])).
% 0.76/0.62  fof(f46,plain,(
% 0.76/0.62    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1)) )),
% 0.76/0.62    inference(resolution,[],[f45,f27])).
% 0.76/0.62  fof(f27,plain,(
% 0.76/0.62    r1_tarski(sK1,sK2)),
% 0.76/0.62    inference(cnf_transformation,[],[f14])).
% 0.76/0.62  fof(f45,plain,(
% 0.76/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(X2,X1)) )),
% 0.76/0.62    inference(superposition,[],[f42,f34])).
% 0.76/0.62  fof(f34,plain,(
% 0.76/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.76/0.62    inference(cnf_transformation,[],[f10])).
% 0.76/0.62  fof(f10,plain,(
% 0.76/0.62    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.76/0.62    inference(ennf_transformation,[],[f2])).
% 0.76/0.62  fof(f2,axiom,(
% 0.76/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.76/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.76/0.62  fof(f42,plain,(
% 0.76/0.62    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 0.76/0.62    inference(equality_resolution,[],[f36])).
% 0.76/0.62  fof(f36,plain,(
% 0.76/0.62    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.76/0.62    inference(cnf_transformation,[],[f23])).
% 0.76/0.62  fof(f23,plain,(
% 0.76/0.62    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.76/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).
% 0.76/0.62  fof(f22,plain,(
% 0.76/0.62    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.76/0.62    introduced(choice_axiom,[])).
% 0.76/0.62  fof(f21,plain,(
% 0.76/0.62    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.76/0.62    inference(rectify,[],[f20])).
% 0.76/0.62  fof(f20,plain,(
% 0.76/0.62    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.76/0.62    inference(flattening,[],[f19])).
% 0.76/0.62  % (20716)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.76/0.63  % (20718)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.76/0.63  % (20716)Refutation not found, incomplete strategy% (20716)------------------------------
% 0.76/0.63  % (20716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.76/0.63  fof(f19,plain,(
% 0.76/0.63    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.76/0.63    inference(nnf_transformation,[],[f1])).
% 0.76/0.63  fof(f1,axiom,(
% 0.76/0.63    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.76/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.76/0.63  fof(f73,plain,(
% 0.76/0.63    ~r2_hidden(sK3(sK0,sK1),sK2)),
% 0.76/0.63    inference(subsumption_resolution,[],[f72,f29])).
% 0.76/0.63  fof(f72,plain,(
% 0.76/0.63    v1_tops_2(sK1,sK0) | ~r2_hidden(sK3(sK0,sK1),sK2)),
% 0.76/0.63    inference(subsumption_resolution,[],[f70,f57])).
% 0.76/0.63  fof(f57,plain,(
% 0.76/0.63    ~v3_pre_topc(sK3(sK0,sK1),sK0)),
% 0.76/0.63    inference(subsumption_resolution,[],[f56,f24])).
% 0.76/0.63  fof(f56,plain,(
% 0.76/0.63    ~v3_pre_topc(sK3(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.76/0.63    inference(subsumption_resolution,[],[f54,f29])).
% 0.76/0.63  fof(f54,plain,(
% 0.76/0.63    ~v3_pre_topc(sK3(sK0,sK1),sK0) | v1_tops_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.76/0.63    inference(resolution,[],[f33,f25])).
% 0.76/0.63  fof(f33,plain,(
% 0.76/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(sK3(X0,X1),X0) | v1_tops_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.76/0.63    inference(cnf_transformation,[],[f18])).
% 0.76/0.63  fof(f70,plain,(
% 0.76/0.63    v3_pre_topc(sK3(sK0,sK1),sK0) | v1_tops_2(sK1,sK0) | ~r2_hidden(sK3(sK0,sK1),sK2)),
% 0.76/0.63    inference(resolution,[],[f69,f25])).
% 0.76/0.63  fof(f69,plain,(
% 0.76/0.63    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v3_pre_topc(sK3(sK0,X0),sK0) | v1_tops_2(X0,sK0) | ~r2_hidden(sK3(sK0,X0),sK2)) )),
% 0.76/0.63    inference(subsumption_resolution,[],[f68,f24])).
% 0.76/0.63  fof(f68,plain,(
% 0.76/0.63    ( ! [X0] : (~r2_hidden(sK3(sK0,X0),sK2) | v3_pre_topc(sK3(sK0,X0),sK0) | v1_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) )),
% 0.76/0.63    inference(resolution,[],[f67,f31])).
% 0.76/0.63  fof(f31,plain,(
% 0.76/0.63    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.76/0.63    inference(cnf_transformation,[],[f18])).
% 0.76/0.63  fof(f67,plain,(
% 0.76/0.63    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,sK2) | v3_pre_topc(X1,sK0)) )),
% 0.76/0.63    inference(subsumption_resolution,[],[f66,f24])).
% 0.76/0.63  fof(f66,plain,(
% 0.76/0.63    ( ! [X1] : (~r2_hidden(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X1,sK0) | ~l1_pre_topc(sK0)) )),
% 0.76/0.63    inference(subsumption_resolution,[],[f65,f28])).
% 0.76/0.63  fof(f28,plain,(
% 0.76/0.63    v1_tops_2(sK2,sK0)),
% 0.76/0.63    inference(cnf_transformation,[],[f14])).
% 0.76/0.63  fof(f65,plain,(
% 0.76/0.63    ( ! [X1] : (~r2_hidden(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_2(sK2,sK0) | v3_pre_topc(X1,sK0) | ~l1_pre_topc(sK0)) )),
% 0.76/0.63    inference(resolution,[],[f30,f26])).
% 0.76/0.63  fof(f26,plain,(
% 0.76/0.63    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.76/0.63    inference(cnf_transformation,[],[f14])).
% 0.76/0.63  fof(f30,plain,(
% 0.76/0.63    ( ! [X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_2(X1,X0) | v3_pre_topc(X3,X0) | ~l1_pre_topc(X0)) )),
% 0.76/0.63    inference(cnf_transformation,[],[f18])).
% 0.76/0.63  % SZS output end Proof for theBenchmark
% 0.76/0.63  % (20734)------------------------------
% 0.76/0.63  % (20734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.76/0.63  % (20734)Termination reason: Refutation
% 0.76/0.63  
% 0.76/0.63  % (20734)Memory used [KB]: 1663
% 0.76/0.63  % (20734)Time elapsed: 0.069 s
% 0.76/0.63  % (20734)------------------------------
% 0.76/0.63  % (20734)------------------------------
% 0.76/0.63  % (20581)Success in time 0.275 s
%------------------------------------------------------------------------------
