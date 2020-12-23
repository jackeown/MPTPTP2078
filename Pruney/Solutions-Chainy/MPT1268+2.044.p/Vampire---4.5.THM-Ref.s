%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:32 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :  108 (1176 expanded)
%              Number of leaves         :   17 ( 334 expanded)
%              Depth                    :   33
%              Number of atoms          :  459 (10243 expanded)
%              Number of equality atoms :   47 (1456 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f754,plain,(
    $false ),
    inference(subsumption_resolution,[],[f741,f657])).

fof(f657,plain,(
    k1_xboole_0 != sK4 ),
    inference(subsumption_resolution,[],[f55,f653])).

fof(f653,plain,(
    v2_tops_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f652,f50])).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ( k1_xboole_0 != sK4
        & v3_pre_topc(sK4,sK2)
        & r1_tarski(sK4,sK3)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) )
      | ~ v2_tops_1(sK3,sK2) )
    & ( ! [X3] :
          ( k1_xboole_0 = X3
          | ~ v3_pre_topc(X3,sK2)
          | ~ r1_tarski(X3,sK3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
      | v2_tops_1(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f31,f34,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( k1_xboole_0 != X2
                  & v3_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_1(X1,X0) )
            & ( ! [X3] :
                  ( k1_xboole_0 = X3
                  | ~ v3_pre_topc(X3,X0)
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,sK2)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
            | ~ v2_tops_1(X1,sK2) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,sK2)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
            | v2_tops_1(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

% (24436)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f33,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( k1_xboole_0 != X2
              & v3_pre_topc(X2,sK2)
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          | ~ v2_tops_1(X1,sK2) )
        & ( ! [X3] :
              ( k1_xboole_0 = X3
              | ~ v3_pre_topc(X3,sK2)
              | ~ r1_tarski(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
          | v2_tops_1(X1,sK2) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ( ? [X2] :
            ( k1_xboole_0 != X2
            & v3_pre_topc(X2,sK2)
            & r1_tarski(X2,sK3)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
        | ~ v2_tops_1(sK3,sK2) )
      & ( ! [X3] :
            ( k1_xboole_0 = X3
            | ~ v3_pre_topc(X3,sK2)
            | ~ r1_tarski(X3,sK3)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
        | v2_tops_1(sK3,sK2) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X2] :
        ( k1_xboole_0 != X2
        & v3_pre_topc(X2,sK2)
        & r1_tarski(X2,sK3)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( k1_xboole_0 != sK4
      & v3_pre_topc(sK4,sK2)
      & r1_tarski(sK4,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,X0)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f30])).

% (24433)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v3_pre_topc(X2,X0)
                      & r1_tarski(X2,X1) )
                   => k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & r1_tarski(X2,X1) )
                 => k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

fof(f652,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tops_1(sK3,sK2) ),
    inference(trivial_inequality_removal,[],[f649])).

fof(f649,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tops_1(sK3,sK2) ),
    inference(superposition,[],[f240,f426])).

fof(f426,plain,(
    k1_xboole_0 = k1_tops_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f425,f49])).

fof(f49,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f425,plain,
    ( k1_xboole_0 = k1_tops_1(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f424,f50])).

fof(f424,plain,
    ( k1_xboole_0 = k1_tops_1(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(duplicate_literal_removal,[],[f423])).

fof(f423,plain,
    ( k1_xboole_0 = k1_tops_1(sK2,sK3)
    | k1_xboole_0 = k1_tops_1(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f418,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f418,plain,
    ( v2_tops_1(sK3,sK2)
    | k1_xboole_0 = k1_tops_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f415,f102])).

fof(f102,plain,(
    r1_tarski(k1_tops_1(sK2,sK3),sK3) ),
    inference(resolution,[],[f101,f50])).

fof(f101,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_tarski(k1_tops_1(sK2,X0),X0) ) ),
    inference(resolution,[],[f57,f49])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

% (24430)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f415,plain,
    ( k1_xboole_0 = k1_tops_1(sK2,sK3)
    | v2_tops_1(sK3,sK2)
    | ~ r1_tarski(k1_tops_1(sK2,sK3),sK3) ),
    inference(resolution,[],[f286,f50])).

fof(f286,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | k1_xboole_0 = k1_tops_1(sK2,X2)
      | v2_tops_1(sK3,sK2)
      | ~ r1_tarski(k1_tops_1(sK2,X2),sK3) ) ),
    inference(resolution,[],[f284,f179])).

fof(f179,plain,(
    ! [X0] :
      ( v3_pre_topc(k1_tops_1(sK2,X0),sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f178,f48])).

fof(f48,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

% (24423)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f178,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v3_pre_topc(k1_tops_1(sK2,X0),sK2)
      | ~ v2_pre_topc(sK2) ) ),
    inference(resolution,[],[f68,f49])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f284,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK2)
      | ~ r1_tarski(X0,sK3)
      | k1_xboole_0 = X0
      | v2_tops_1(sK3,sK2) ) ),
    inference(subsumption_resolution,[],[f282,f202])).

fof(f202,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK3)
      | r1_tarski(X0,u1_struct_0(sK2)) ) ),
    inference(duplicate_literal_removal,[],[f199])).

fof(f199,plain,(
    ! [X0] :
      ( r1_tarski(X0,u1_struct_0(sK2))
      | ~ r1_tarski(X0,sK3)
      | r1_tarski(X0,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f198,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f198,plain,(
    ! [X21,X22] :
      ( r2_hidden(sK6(X21,X22),u1_struct_0(sK2))
      | r1_tarski(X21,X22)
      | ~ r1_tarski(X21,sK3) ) ),
    inference(resolution,[],[f94,f79])).

fof(f79,plain,(
    r1_tarski(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f72,f50])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f94,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_tarski(X3,X5)
      | r1_tarski(X2,X4)
      | r2_hidden(sK6(X2,X4),X5)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f85,f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1),X2)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f69,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f282,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK2)
      | ~ r1_tarski(X0,sK3)
      | k1_xboole_0 = X0
      | v2_tops_1(sK3,sK2)
      | ~ r1_tarski(X0,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f51,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f51,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_pre_topc(X3,sK2)
      | ~ r1_tarski(X3,sK3)
      | k1_xboole_0 = X3
      | v2_tops_1(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f240,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_tops_1(sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v2_tops_1(X0,sK2) ) ),
    inference(resolution,[],[f59,f49])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,
    ( ~ v2_tops_1(sK3,sK2)
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f35])).

fof(f741,plain,(
    k1_xboole_0 = sK4 ),
    inference(resolution,[],[f730,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
        & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
        & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
          & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
          & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_mcart_1)).

fof(f730,plain,(
    ! [X5] : r1_tarski(sK4,X5) ),
    inference(subsumption_resolution,[],[f727,f56])).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f727,plain,(
    ! [X5] :
      ( r1_tarski(sK4,X5)
      | ~ r1_tarski(k1_xboole_0,sK6(sK4,X5)) ) ),
    inference(resolution,[],[f719,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f719,plain,(
    ! [X0] :
      ( r2_hidden(sK6(sK4,X0),k1_xboole_0)
      | r1_tarski(sK4,X0) ) ),
    inference(resolution,[],[f716,f438])).

fof(f438,plain,(
    ! [X0] :
      ( ~ sP0(X0,sK3,sK2)
      | r2_hidden(X0,k1_xboole_0) ) ),
    inference(backward_demodulation,[],[f150,f426])).

fof(f150,plain,(
    ! [X0] :
      ( ~ sP0(X0,sK3,sK2)
      | r2_hidden(X0,k1_tops_1(sK2,sK3)) ) ),
    inference(resolution,[],[f148,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r2_hidden(X2,k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X2,k1_tops_1(X0,X1))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X2,k1_tops_1(X0,X1)) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X1,k1_tops_1(X0,X2))
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f148,plain,(
    ! [X0] : sP1(sK2,sK3,X0) ),
    inference(resolution,[],[f147,f50])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(sK2,X0,X1) ) ),
    inference(subsumption_resolution,[],[f146,f48])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(sK2,X0,X1)
      | ~ v2_pre_topc(sK2) ) ),
    inference(resolution,[],[f67,f49])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X2,X1)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP1(X0,X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f18,f27,f26])).

fof(f26,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ? [X3] :
          ( r2_hidden(X1,X3)
          & r1_tarski(X3,X2)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f716,plain,(
    ! [X0] :
      ( sP0(sK6(sK4,X0),sK3,sK2)
      | r1_tarski(sK4,X0) ) ),
    inference(resolution,[],[f698,f655])).

fof(f655,plain,(
    r1_tarski(sK4,sK3) ),
    inference(subsumption_resolution,[],[f53,f653])).

fof(f53,plain,
    ( ~ v2_tops_1(sK3,sK2)
    | r1_tarski(sK4,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f698,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK4,X0)
      | sP0(sK6(sK4,X1),X0,sK2)
      | r1_tarski(sK4,X1) ) ),
    inference(resolution,[],[f662,f70])).

fof(f662,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK4)
      | ~ r1_tarski(sK4,X0)
      | sP0(X1,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f661,f658])).

fof(f658,plain,(
    r1_tarski(sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f655,f202])).

fof(f661,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK4,X0)
      | ~ r2_hidden(X1,sK4)
      | sP0(X1,X0,sK2)
      | ~ r1_tarski(sK4,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f656,f365])).

fof(f365,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ v3_pre_topc(X3,X5)
      | ~ r1_tarski(X3,X4)
      | ~ r2_hidden(X2,X3)
      | sP0(X2,X4,X5)
      | ~ r1_tarski(X3,u1_struct_0(X5)) ) ),
    inference(resolution,[],[f66,f73])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r2_hidden(X0,X3)
      | ~ r1_tarski(X3,X1)
      | ~ v3_pre_topc(X3,X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X0,X3)
            | ~ r1_tarski(X3,X1)
            | ~ v3_pre_topc(X3,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ( r2_hidden(X0,sK5(X0,X1,X2))
          & r1_tarski(sK5(X0,X1,X2),X1)
          & v3_pre_topc(sK5(X0,X1,X2),X2)
          & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X0,X4)
          & r1_tarski(X4,X1)
          & v3_pre_topc(X4,X2)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r2_hidden(X0,sK5(X0,X1,X2))
        & r1_tarski(sK5(X0,X1,X2),X1)
        & v3_pre_topc(sK5(X0,X1,X2),X2)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X0,X3)
            | ~ r1_tarski(X3,X1)
            | ~ v3_pre_topc(X3,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ? [X4] :
            ( r2_hidden(X0,X4)
            & r1_tarski(X4,X1)
            & v3_pre_topc(X4,X2)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ! [X3] :
            ( ~ r2_hidden(X1,X3)
            | ~ r1_tarski(X3,X2)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ? [X3] :
            ( r2_hidden(X1,X3)
            & r1_tarski(X3,X2)
            & v3_pre_topc(X3,X0)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f656,plain,(
    v3_pre_topc(sK4,sK2) ),
    inference(subsumption_resolution,[],[f54,f653])).

fof(f54,plain,
    ( ~ v2_tops_1(sK3,sK2)
    | v3_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:42:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (24419)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (24413)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.34/0.53  % (24416)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.34/0.53  % (24435)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.34/0.53  % (24421)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.34/0.53  % (24415)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.34/0.54  % (24417)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.34/0.54  % (24414)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.34/0.54  % (24434)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.34/0.54  % (24425)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.34/0.54  % (24424)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.54  % (24437)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.34/0.54  % (24426)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.34/0.54  % (24412)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.34/0.54  % (24439)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.34/0.55  % (24429)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.34/0.55  % (24438)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.34/0.55  % (24418)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.34/0.55  % (24441)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.34/0.55  % (24440)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.34/0.55  % (24427)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.34/0.55  % (24431)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.34/0.55  % (24428)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.34/0.55  % (24422)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.34/0.55  % (24419)Refutation found. Thanks to Tanya!
% 1.34/0.55  % SZS status Theorem for theBenchmark
% 1.34/0.55  % SZS output start Proof for theBenchmark
% 1.34/0.55  fof(f754,plain,(
% 1.34/0.55    $false),
% 1.34/0.55    inference(subsumption_resolution,[],[f741,f657])).
% 1.34/0.55  fof(f657,plain,(
% 1.34/0.55    k1_xboole_0 != sK4),
% 1.34/0.55    inference(subsumption_resolution,[],[f55,f653])).
% 1.34/0.55  fof(f653,plain,(
% 1.34/0.55    v2_tops_1(sK3,sK2)),
% 1.34/0.55    inference(subsumption_resolution,[],[f652,f50])).
% 1.34/0.55  fof(f50,plain,(
% 1.34/0.55    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.34/0.55    inference(cnf_transformation,[],[f35])).
% 1.34/0.55  fof(f35,plain,(
% 1.34/0.55    (((k1_xboole_0 != sK4 & v3_pre_topc(sK4,sK2) & r1_tarski(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) | ~v2_tops_1(sK3,sK2)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK2) | ~r1_tarski(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) | v2_tops_1(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2)),
% 1.34/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f31,f34,f33,f32])).
% 1.34/0.55  fof(f32,plain,(
% 1.34/0.55    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK2) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) | ~v2_tops_1(X1,sK2)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK2) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) | v2_tops_1(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 1.34/0.55    introduced(choice_axiom,[])).
% 1.34/0.55  % (24436)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.34/0.55  fof(f33,plain,(
% 1.34/0.55    ? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK2) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) | ~v2_tops_1(X1,sK2)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK2) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) | v2_tops_1(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK2) & r1_tarski(X2,sK3) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) | ~v2_tops_1(sK3,sK2)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK2) | ~r1_tarski(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) | v2_tops_1(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))))),
% 1.34/0.55    introduced(choice_axiom,[])).
% 1.34/0.55  fof(f34,plain,(
% 1.34/0.55    ? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK2) & r1_tarski(X2,sK3) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) => (k1_xboole_0 != sK4 & v3_pre_topc(sK4,sK2) & r1_tarski(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))))),
% 1.34/0.55    introduced(choice_axiom,[])).
% 1.34/0.55  fof(f31,plain,(
% 1.34/0.55    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.34/0.55    inference(rectify,[],[f30])).
% 1.55/0.56  % (24433)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.55/0.56  fof(f30,plain,(
% 1.55/0.56    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.55/0.56    inference(flattening,[],[f29])).
% 1.55/0.56  fof(f29,plain,(
% 1.55/0.56    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.55/0.56    inference(nnf_transformation,[],[f14])).
% 1.55/0.56  fof(f14,plain,(
% 1.55/0.56    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.55/0.56    inference(flattening,[],[f13])).
% 1.55/0.56  fof(f13,plain,(
% 1.55/0.56    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.55/0.56    inference(ennf_transformation,[],[f12])).
% 1.55/0.56  fof(f12,negated_conjecture,(
% 1.55/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 1.55/0.56    inference(negated_conjecture,[],[f11])).
% 1.55/0.56  fof(f11,conjecture,(
% 1.55/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).
% 1.55/0.56  fof(f652,plain,(
% 1.55/0.56    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | v2_tops_1(sK3,sK2)),
% 1.55/0.56    inference(trivial_inequality_removal,[],[f649])).
% 1.55/0.56  fof(f649,plain,(
% 1.55/0.56    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | v2_tops_1(sK3,sK2)),
% 1.55/0.56    inference(superposition,[],[f240,f426])).
% 1.55/0.56  fof(f426,plain,(
% 1.55/0.56    k1_xboole_0 = k1_tops_1(sK2,sK3)),
% 1.55/0.56    inference(subsumption_resolution,[],[f425,f49])).
% 1.55/0.56  fof(f49,plain,(
% 1.55/0.56    l1_pre_topc(sK2)),
% 1.55/0.56    inference(cnf_transformation,[],[f35])).
% 1.55/0.56  fof(f425,plain,(
% 1.55/0.56    k1_xboole_0 = k1_tops_1(sK2,sK3) | ~l1_pre_topc(sK2)),
% 1.55/0.56    inference(subsumption_resolution,[],[f424,f50])).
% 1.55/0.56  fof(f424,plain,(
% 1.55/0.56    k1_xboole_0 = k1_tops_1(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 1.55/0.56    inference(duplicate_literal_removal,[],[f423])).
% 1.55/0.56  fof(f423,plain,(
% 1.55/0.56    k1_xboole_0 = k1_tops_1(sK2,sK3) | k1_xboole_0 = k1_tops_1(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 1.55/0.56    inference(resolution,[],[f418,f58])).
% 1.55/0.56  fof(f58,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f36])).
% 1.55/0.56  fof(f36,plain,(
% 1.55/0.56    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.55/0.56    inference(nnf_transformation,[],[f16])).
% 1.55/0.56  fof(f16,plain,(
% 1.55/0.56    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.55/0.56    inference(ennf_transformation,[],[f10])).
% 1.55/0.56  fof(f10,axiom,(
% 1.55/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 1.55/0.56  fof(f418,plain,(
% 1.55/0.56    v2_tops_1(sK3,sK2) | k1_xboole_0 = k1_tops_1(sK2,sK3)),
% 1.55/0.56    inference(subsumption_resolution,[],[f415,f102])).
% 1.55/0.56  fof(f102,plain,(
% 1.55/0.56    r1_tarski(k1_tops_1(sK2,sK3),sK3)),
% 1.55/0.56    inference(resolution,[],[f101,f50])).
% 1.55/0.56  fof(f101,plain,(
% 1.55/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | r1_tarski(k1_tops_1(sK2,X0),X0)) )),
% 1.55/0.56    inference(resolution,[],[f57,f49])).
% 1.55/0.56  fof(f57,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f15])).
% 1.55/0.56  % (24430)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.55/0.56  fof(f15,plain,(
% 1.55/0.56    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.55/0.56    inference(ennf_transformation,[],[f8])).
% 1.55/0.56  fof(f8,axiom,(
% 1.55/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 1.55/0.56  fof(f415,plain,(
% 1.55/0.56    k1_xboole_0 = k1_tops_1(sK2,sK3) | v2_tops_1(sK3,sK2) | ~r1_tarski(k1_tops_1(sK2,sK3),sK3)),
% 1.55/0.56    inference(resolution,[],[f286,f50])).
% 1.55/0.56  fof(f286,plain,(
% 1.55/0.56    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | k1_xboole_0 = k1_tops_1(sK2,X2) | v2_tops_1(sK3,sK2) | ~r1_tarski(k1_tops_1(sK2,X2),sK3)) )),
% 1.55/0.56    inference(resolution,[],[f284,f179])).
% 1.55/0.56  fof(f179,plain,(
% 1.55/0.56    ( ! [X0] : (v3_pre_topc(k1_tops_1(sK2,X0),sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.55/0.56    inference(subsumption_resolution,[],[f178,f48])).
% 1.55/0.56  fof(f48,plain,(
% 1.55/0.56    v2_pre_topc(sK2)),
% 1.55/0.56    inference(cnf_transformation,[],[f35])).
% 1.55/0.56  % (24423)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.55/0.56  fof(f178,plain,(
% 1.55/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | v3_pre_topc(k1_tops_1(sK2,X0),sK2) | ~v2_pre_topc(sK2)) )),
% 1.55/0.56    inference(resolution,[],[f68,f49])).
% 1.55/0.56  fof(f68,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~v2_pre_topc(X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f20])).
% 1.55/0.56  fof(f20,plain,(
% 1.55/0.56    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.55/0.56    inference(flattening,[],[f19])).
% 1.55/0.56  fof(f19,plain,(
% 1.55/0.56    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.55/0.56    inference(ennf_transformation,[],[f7])).
% 1.55/0.56  fof(f7,axiom,(
% 1.55/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 1.55/0.56  fof(f284,plain,(
% 1.55/0.56    ( ! [X0] : (~v3_pre_topc(X0,sK2) | ~r1_tarski(X0,sK3) | k1_xboole_0 = X0 | v2_tops_1(sK3,sK2)) )),
% 1.55/0.56    inference(subsumption_resolution,[],[f282,f202])).
% 1.55/0.56  fof(f202,plain,(
% 1.55/0.56    ( ! [X0] : (~r1_tarski(X0,sK3) | r1_tarski(X0,u1_struct_0(sK2))) )),
% 1.55/0.56    inference(duplicate_literal_removal,[],[f199])).
% 1.55/0.56  fof(f199,plain,(
% 1.55/0.56    ( ! [X0] : (r1_tarski(X0,u1_struct_0(sK2)) | ~r1_tarski(X0,sK3) | r1_tarski(X0,u1_struct_0(sK2))) )),
% 1.55/0.56    inference(resolution,[],[f198,f71])).
% 1.55/0.56  fof(f71,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f46])).
% 1.55/0.56  fof(f46,plain,(
% 1.55/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.55/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f45])).
% 1.55/0.56  fof(f45,plain,(
% 1.55/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.55/0.56    introduced(choice_axiom,[])).
% 1.55/0.56  fof(f44,plain,(
% 1.55/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.55/0.56    inference(rectify,[],[f43])).
% 1.55/0.56  fof(f43,plain,(
% 1.55/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.55/0.56    inference(nnf_transformation,[],[f21])).
% 1.55/0.56  fof(f21,plain,(
% 1.55/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.55/0.56    inference(ennf_transformation,[],[f1])).
% 1.55/0.56  fof(f1,axiom,(
% 1.55/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.55/0.56  fof(f198,plain,(
% 1.55/0.56    ( ! [X21,X22] : (r2_hidden(sK6(X21,X22),u1_struct_0(sK2)) | r1_tarski(X21,X22) | ~r1_tarski(X21,sK3)) )),
% 1.55/0.56    inference(resolution,[],[f94,f79])).
% 1.55/0.56  fof(f79,plain,(
% 1.55/0.56    r1_tarski(sK3,u1_struct_0(sK2))),
% 1.55/0.56    inference(resolution,[],[f72,f50])).
% 1.55/0.56  fof(f72,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f47])).
% 1.55/0.56  fof(f47,plain,(
% 1.55/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.55/0.56    inference(nnf_transformation,[],[f4])).
% 1.55/0.56  fof(f4,axiom,(
% 1.55/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.55/0.56  fof(f94,plain,(
% 1.55/0.56    ( ! [X4,X2,X5,X3] : (~r1_tarski(X3,X5) | r1_tarski(X2,X4) | r2_hidden(sK6(X2,X4),X5) | ~r1_tarski(X2,X3)) )),
% 1.55/0.56    inference(resolution,[],[f85,f69])).
% 1.55/0.56  fof(f69,plain,(
% 1.55/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f46])).
% 1.55/0.56  fof(f85,plain,(
% 1.55/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1),X2) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1)) )),
% 1.55/0.56    inference(resolution,[],[f69,f70])).
% 1.55/0.56  fof(f70,plain,(
% 1.55/0.56    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f46])).
% 1.55/0.56  fof(f282,plain,(
% 1.55/0.56    ( ! [X0] : (~v3_pre_topc(X0,sK2) | ~r1_tarski(X0,sK3) | k1_xboole_0 = X0 | v2_tops_1(sK3,sK2) | ~r1_tarski(X0,u1_struct_0(sK2))) )),
% 1.55/0.56    inference(resolution,[],[f51,f73])).
% 1.55/0.56  fof(f73,plain,(
% 1.55/0.56    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f47])).
% 1.55/0.56  fof(f51,plain,(
% 1.55/0.56    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(X3,sK2) | ~r1_tarski(X3,sK3) | k1_xboole_0 = X3 | v2_tops_1(sK3,sK2)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f35])).
% 1.55/0.56  fof(f240,plain,(
% 1.55/0.56    ( ! [X0] : (k1_xboole_0 != k1_tops_1(sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | v2_tops_1(X0,sK2)) )),
% 1.55/0.56    inference(resolution,[],[f59,f49])).
% 1.55/0.56  fof(f59,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_1(X1,X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f36])).
% 1.55/0.56  fof(f55,plain,(
% 1.55/0.56    ~v2_tops_1(sK3,sK2) | k1_xboole_0 != sK4),
% 1.55/0.56    inference(cnf_transformation,[],[f35])).
% 1.55/0.56  fof(f741,plain,(
% 1.55/0.56    k1_xboole_0 = sK4),
% 1.55/0.56    inference(resolution,[],[f730,f76])).
% 1.55/0.56  fof(f76,plain,(
% 1.55/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X0) )),
% 1.55/0.56    inference(cnf_transformation,[],[f25])).
% 1.55/0.56  fof(f25,plain,(
% 1.55/0.56    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k3_zfmisc_1(X2,X0,X1)) & ~r1_tarski(X0,k3_zfmisc_1(X1,X2,X0)) & ~r1_tarski(X0,k3_zfmisc_1(X0,X1,X2))))),
% 1.55/0.56    inference(ennf_transformation,[],[f6])).
% 1.55/0.56  fof(f6,axiom,(
% 1.55/0.56    ! [X0,X1,X2] : (~(~r1_tarski(X0,k3_zfmisc_1(X2,X0,X1)) & ~r1_tarski(X0,k3_zfmisc_1(X1,X2,X0)) & ~r1_tarski(X0,k3_zfmisc_1(X0,X1,X2))) => k1_xboole_0 = X0)),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_mcart_1)).
% 1.55/0.56  fof(f730,plain,(
% 1.55/0.56    ( ! [X5] : (r1_tarski(sK4,X5)) )),
% 1.55/0.56    inference(subsumption_resolution,[],[f727,f56])).
% 1.55/0.56  fof(f56,plain,(
% 1.55/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f3])).
% 1.55/0.56  fof(f3,axiom,(
% 1.55/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.55/0.56  fof(f727,plain,(
% 1.55/0.56    ( ! [X5] : (r1_tarski(sK4,X5) | ~r1_tarski(k1_xboole_0,sK6(sK4,X5))) )),
% 1.55/0.56    inference(resolution,[],[f719,f74])).
% 1.55/0.56  fof(f74,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f22])).
% 1.55/0.56  fof(f22,plain,(
% 1.55/0.56    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.55/0.56    inference(ennf_transformation,[],[f5])).
% 1.55/0.56  fof(f5,axiom,(
% 1.55/0.56    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.55/0.56  fof(f719,plain,(
% 1.55/0.56    ( ! [X0] : (r2_hidden(sK6(sK4,X0),k1_xboole_0) | r1_tarski(sK4,X0)) )),
% 1.55/0.56    inference(resolution,[],[f716,f438])).
% 1.55/0.56  fof(f438,plain,(
% 1.55/0.56    ( ! [X0] : (~sP0(X0,sK3,sK2) | r2_hidden(X0,k1_xboole_0)) )),
% 1.55/0.56    inference(backward_demodulation,[],[f150,f426])).
% 1.55/0.56  fof(f150,plain,(
% 1.55/0.56    ( ! [X0] : (~sP0(X0,sK3,sK2) | r2_hidden(X0,k1_tops_1(sK2,sK3))) )),
% 1.55/0.56    inference(resolution,[],[f148,f61])).
% 1.55/0.56  fof(f61,plain,(
% 1.55/0.56    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r2_hidden(X2,k1_tops_1(X0,X1))) )),
% 1.55/0.56    inference(cnf_transformation,[],[f38])).
% 1.55/0.56  fof(f38,plain,(
% 1.55/0.56    ! [X0,X1,X2] : (((r2_hidden(X2,k1_tops_1(X0,X1)) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X2,k1_tops_1(X0,X1)))) | ~sP1(X0,X1,X2))),
% 1.55/0.56    inference(rectify,[],[f37])).
% 1.55/0.56  fof(f37,plain,(
% 1.55/0.56    ! [X0,X2,X1] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~sP1(X0,X2,X1))),
% 1.55/0.56    inference(nnf_transformation,[],[f27])).
% 1.55/0.56  fof(f27,plain,(
% 1.55/0.56    ! [X0,X2,X1] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 1.55/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.55/0.56  fof(f148,plain,(
% 1.55/0.56    ( ! [X0] : (sP1(sK2,sK3,X0)) )),
% 1.55/0.56    inference(resolution,[],[f147,f50])).
% 1.55/0.56  fof(f147,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(sK2,X0,X1)) )),
% 1.55/0.56    inference(subsumption_resolution,[],[f146,f48])).
% 1.55/0.56  fof(f146,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(sK2,X0,X1) | ~v2_pre_topc(sK2)) )),
% 1.55/0.56    inference(resolution,[],[f67,f49])).
% 1.55/0.56  fof(f67,plain,(
% 1.55/0.56    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X2,X1) | ~v2_pre_topc(X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f28])).
% 1.55/0.56  fof(f28,plain,(
% 1.55/0.56    ! [X0] : (! [X1,X2] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.55/0.56    inference(definition_folding,[],[f18,f27,f26])).
% 1.55/0.56  fof(f26,plain,(
% 1.55/0.56    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.55/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.55/0.56  fof(f18,plain,(
% 1.55/0.56    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.55/0.56    inference(flattening,[],[f17])).
% 1.55/0.56  fof(f17,plain,(
% 1.55/0.56    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.55/0.56    inference(ennf_transformation,[],[f9])).
% 1.55/0.56  fof(f9,axiom,(
% 1.55/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).
% 1.55/0.56  fof(f716,plain,(
% 1.55/0.56    ( ! [X0] : (sP0(sK6(sK4,X0),sK3,sK2) | r1_tarski(sK4,X0)) )),
% 1.55/0.56    inference(resolution,[],[f698,f655])).
% 1.55/0.56  fof(f655,plain,(
% 1.55/0.56    r1_tarski(sK4,sK3)),
% 1.55/0.56    inference(subsumption_resolution,[],[f53,f653])).
% 1.55/0.56  fof(f53,plain,(
% 1.55/0.56    ~v2_tops_1(sK3,sK2) | r1_tarski(sK4,sK3)),
% 1.55/0.56    inference(cnf_transformation,[],[f35])).
% 1.55/0.56  fof(f698,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~r1_tarski(sK4,X0) | sP0(sK6(sK4,X1),X0,sK2) | r1_tarski(sK4,X1)) )),
% 1.55/0.56    inference(resolution,[],[f662,f70])).
% 1.55/0.56  fof(f662,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~r2_hidden(X1,sK4) | ~r1_tarski(sK4,X0) | sP0(X1,X0,sK2)) )),
% 1.55/0.56    inference(subsumption_resolution,[],[f661,f658])).
% 1.55/0.56  fof(f658,plain,(
% 1.55/0.56    r1_tarski(sK4,u1_struct_0(sK2))),
% 1.55/0.56    inference(resolution,[],[f655,f202])).
% 1.55/0.56  fof(f661,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~r1_tarski(sK4,X0) | ~r2_hidden(X1,sK4) | sP0(X1,X0,sK2) | ~r1_tarski(sK4,u1_struct_0(sK2))) )),
% 1.55/0.56    inference(resolution,[],[f656,f365])).
% 1.55/0.56  fof(f365,plain,(
% 1.55/0.56    ( ! [X4,X2,X5,X3] : (~v3_pre_topc(X3,X5) | ~r1_tarski(X3,X4) | ~r2_hidden(X2,X3) | sP0(X2,X4,X5) | ~r1_tarski(X3,u1_struct_0(X5))) )),
% 1.55/0.56    inference(resolution,[],[f66,f73])).
% 1.55/0.56  fof(f66,plain,(
% 1.55/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~r2_hidden(X0,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X2) | sP0(X0,X1,X2)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f42])).
% 1.55/0.56  fof(f42,plain,(
% 1.55/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r2_hidden(X0,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & ((r2_hidden(X0,sK5(X0,X1,X2)) & r1_tarski(sK5(X0,X1,X2),X1) & v3_pre_topc(sK5(X0,X1,X2),X2) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 1.55/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).
% 1.55/0.56  fof(f41,plain,(
% 1.55/0.56    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X0,X4) & r1_tarski(X4,X1) & v3_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) => (r2_hidden(X0,sK5(X0,X1,X2)) & r1_tarski(sK5(X0,X1,X2),X1) & v3_pre_topc(sK5(X0,X1,X2),X2) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))))),
% 1.55/0.56    introduced(choice_axiom,[])).
% 1.55/0.56  fof(f40,plain,(
% 1.55/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r2_hidden(X0,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & (? [X4] : (r2_hidden(X0,X4) & r1_tarski(X4,X1) & v3_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 1.55/0.56    inference(rectify,[],[f39])).
% 1.55/0.56  fof(f39,plain,(
% 1.55/0.56    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X2,X0)))),
% 1.55/0.56    inference(nnf_transformation,[],[f26])).
% 1.55/0.56  fof(f656,plain,(
% 1.55/0.56    v3_pre_topc(sK4,sK2)),
% 1.55/0.56    inference(subsumption_resolution,[],[f54,f653])).
% 1.55/0.56  fof(f54,plain,(
% 1.55/0.56    ~v2_tops_1(sK3,sK2) | v3_pre_topc(sK4,sK2)),
% 1.55/0.56    inference(cnf_transformation,[],[f35])).
% 1.55/0.56  % SZS output end Proof for theBenchmark
% 1.55/0.56  % (24419)------------------------------
% 1.55/0.56  % (24419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (24419)Termination reason: Refutation
% 1.55/0.56  
% 1.55/0.56  % (24419)Memory used [KB]: 6652
% 1.55/0.56  % (24419)Time elapsed: 0.127 s
% 1.55/0.56  % (24419)------------------------------
% 1.55/0.56  % (24419)------------------------------
% 1.55/0.56  % (24433)Refutation not found, incomplete strategy% (24433)------------------------------
% 1.55/0.56  % (24433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (24433)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.56  
% 1.55/0.56  % (24433)Memory used [KB]: 1791
% 1.55/0.56  % (24433)Time elapsed: 0.161 s
% 1.55/0.56  % (24433)------------------------------
% 1.55/0.56  % (24433)------------------------------
% 1.55/0.56  % (24411)Success in time 0.201 s
%------------------------------------------------------------------------------
