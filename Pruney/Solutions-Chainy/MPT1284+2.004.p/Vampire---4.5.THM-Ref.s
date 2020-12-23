%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  114 (2829 expanded)
%              Number of leaves         :   14 (1179 expanded)
%              Depth                    :   32
%              Number of atoms          :  450 (24129 expanded)
%              Number of equality atoms :   36 ( 346 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f254,plain,(
    $false ),
    inference(resolution,[],[f253,f62])).

fof(f62,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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

fof(f253,plain,(
    ~ r1_tarski(sK3,sK3) ),
    inference(subsumption_resolution,[],[f230,f252])).

% (14258)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (14250)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% (14269)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% (14264)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% (14253)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% (14251)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% (14261)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% (14262)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% (14245)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% (14245)Refutation not found, incomplete strategy% (14245)------------------------------
% (14245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14245)Termination reason: Refutation not found, incomplete strategy

% (14245)Memory used [KB]: 10618
% (14245)Time elapsed: 0.104 s
% (14245)------------------------------
% (14245)------------------------------
fof(f252,plain,(
    ~ v4_tops_1(sK3,sK1) ),
    inference(global_subsumption,[],[f206,f249])).

fof(f249,plain,
    ( ~ v4_tops_1(sK4,sK2)
    | ~ v4_tops_1(sK3,sK1) ),
    inference(resolution,[],[f248,f207])).

fof(f207,plain,
    ( ~ v5_tops_1(sK4,sK2)
    | ~ v4_tops_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f67,f202])).

fof(f202,plain,(
    v4_pre_topc(sK3,sK1) ),
    inference(global_subsumption,[],[f44,f42,f201])).

fof(f201,plain,
    ( v4_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f198,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f198,plain,
    ( ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_pre_topc(sK3,sK1) ),
    inference(superposition,[],[f78,f192])).

fof(f192,plain,(
    sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) ),
    inference(global_subsumption,[],[f45,f66,f75,f104,f107,f127,f189])).

fof(f189,plain,
    ( ~ r1_tarski(k1_tops_1(sK2,sK4),sK4)
    | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK4 = k2_pre_topc(sK2,k1_tops_1(sK2,sK4))
    | ~ v4_tops_1(sK4,sK2) ),
    inference(resolution,[],[f181,f158])).

fof(f158,plain,
    ( ~ r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,sK4)),sK4)
    | sK4 = k2_pre_topc(sK2,k1_tops_1(sK2,sK4))
    | ~ v4_tops_1(sK4,sK2) ),
    inference(resolution,[],[f154,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f154,plain,
    ( r1_tarski(sK4,k2_pre_topc(sK2,k1_tops_1(sK2,sK4)))
    | ~ v4_tops_1(sK4,sK2) ),
    inference(resolution,[],[f146,f45])).

fof(f146,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v4_tops_1(X1,sK2)
      | r1_tarski(X1,k2_pre_topc(sK2,k1_tops_1(sK2,X1))) ) ),
    inference(resolution,[],[f54,f43])).

fof(f43,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ( ( ~ v4_tops_1(sK3,sK1)
          | ~ v4_pre_topc(sK3,sK1) )
        & v5_tops_1(sK3,sK1) )
      | sP0(sK2,sK4) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f31,f30,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( ~ v4_tops_1(X2,X0)
                          | ~ v4_pre_topc(X2,X0) )
                        & v5_tops_1(X2,X0) )
                      | sP0(X1,X3) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,sK1)
                        | ~ v4_pre_topc(X2,sK1) )
                      & v5_tops_1(X2,sK1) )
                    | sP0(X1,X3) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( ~ v4_tops_1(X2,sK1)
                      | ~ v4_pre_topc(X2,sK1) )
                    & v5_tops_1(X2,sK1) )
                  | sP0(X1,X3) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( ~ v4_tops_1(X2,sK1)
                    | ~ v4_pre_topc(X2,sK1) )
                  & v5_tops_1(X2,sK1) )
                | sP0(sK2,X3) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ( ~ v4_tops_1(X2,sK1)
                  | ~ v4_pre_topc(X2,sK1) )
                & v5_tops_1(X2,sK1) )
              | sP0(sK2,X3) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ? [X3] :
          ( ( ( ( ~ v4_tops_1(sK3,sK1)
                | ~ v4_pre_topc(sK3,sK1) )
              & v5_tops_1(sK3,sK1) )
            | sP0(sK2,X3) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X3] :
        ( ( ( ( ~ v4_tops_1(sK3,sK1)
              | ~ v4_pre_topc(sK3,sK1) )
            & v5_tops_1(sK3,sK1) )
          | sP0(sK2,X3) )
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ( ( ( ~ v4_tops_1(sK3,sK1)
            | ~ v4_pre_topc(sK3,sK1) )
          & v5_tops_1(sK3,sK1) )
        | sP0(sK2,sK4) )
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v4_pre_topc(X2,X0) )
                      & v5_tops_1(X2,X0) )
                    | sP0(X1,X3) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f12,f24])).

fof(f24,plain,(
    ! [X1,X3] :
      ( ( ~ v5_tops_1(X3,X1)
        & v4_tops_1(X3,X1)
        & v4_pre_topc(X3,X1) )
      | ~ sP0(X1,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v4_pre_topc(X2,X0) )
                      & v5_tops_1(X2,X0) )
                    | ( ~ v5_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v4_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v4_pre_topc(X2,X0) )
                      & v5_tops_1(X2,X0) )
                    | ( ~ v5_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v4_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v5_tops_1(X2,X0)
                       => ( v4_tops_1(X2,X0)
                          & v4_pre_topc(X2,X0) ) )
                      & ( ( v4_tops_1(X3,X1)
                          & v4_pre_topc(X3,X1) )
                       => v5_tops_1(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v5_tops_1(X2,X0)
                     => ( v4_tops_1(X2,X0)
                        & v4_pre_topc(X2,X0) ) )
                    & ( ( v4_tops_1(X3,X1)
                        & v4_pre_topc(X3,X1) )
                     => v5_tops_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tops_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).

fof(f181,plain,(
    ! [X0] :
      ( r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,X0)),sK4)
      | ~ r1_tarski(k1_tops_1(sK2,X0),sK4)
      | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(global_subsumption,[],[f43,f180])).

fof(f180,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tops_1(sK2,X0),sK4)
      | r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,X0)),sK4)
      | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2) ) ),
    inference(resolution,[],[f178,f58])).

fof(f178,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r1_tarski(X0,sK4)
      | r1_tarski(k2_pre_topc(sK2,X0),sK4)
      | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) ) ),
    inference(resolution,[],[f175,f108])).

fof(f108,plain,
    ( v4_pre_topc(sK4,sK2)
    | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) ),
    inference(resolution,[],[f104,f64])).

fof(f64,plain,
    ( v5_tops_1(sK3,sK1)
    | v4_pre_topc(sK4,sK2) ),
    inference(resolution,[],[f38,f46])).

fof(f46,plain,
    ( sP0(sK2,sK4)
    | v5_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ v5_tops_1(X1,X0)
        & v4_tops_1(X1,X0)
        & v4_pre_topc(X1,X0) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X1,X3] :
      ( ( ~ v5_tops_1(X3,X1)
        & v4_tops_1(X3,X1)
        & v4_pre_topc(X3,X1) )
      | ~ sP0(X1,X3) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f175,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(sK4,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r1_tarski(X0,sK4)
      | r1_tarski(k2_pre_topc(sK2,X0),sK4) ) ),
    inference(resolution,[],[f166,f45])).

fof(f166,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v4_pre_topc(X3,sK2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r1_tarski(X2,X3)
      | r1_tarski(k2_pre_topc(sK2,X2),X3) ) ),
    inference(resolution,[],[f56,f43])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X2,X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_pre_topc(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X2,X1)
                  & v4_pre_topc(X1,X0) )
               => r1_tarski(k2_pre_topc(X0,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_1)).

fof(f127,plain,
    ( sK4 != k2_pre_topc(sK2,k1_tops_1(sK2,sK4))
    | v5_tops_1(sK4,sK2) ),
    inference(resolution,[],[f118,f45])).

fof(f118,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | k2_pre_topc(sK2,k1_tops_1(sK2,X1)) != X1
      | v5_tops_1(X1,sK2) ) ),
    inference(resolution,[],[f52,f43])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v5_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

fof(f107,plain,
    ( v4_tops_1(sK4,sK2)
    | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) ),
    inference(resolution,[],[f104,f65])).

fof(f65,plain,
    ( v5_tops_1(sK3,sK1)
    | v4_tops_1(sK4,sK2) ),
    inference(resolution,[],[f39,f46])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v4_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f104,plain,
    ( ~ v5_tops_1(sK3,sK1)
    | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) ),
    inference(resolution,[],[f102,f44])).

fof(f102,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v5_tops_1(X0,sK1)
      | k2_pre_topc(sK1,k1_tops_1(sK1,X0)) = X0 ) ),
    inference(resolution,[],[f51,f42])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    r1_tarski(k1_tops_1(sK2,sK4),sK4) ),
    inference(resolution,[],[f72,f45])).

fof(f72,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_tarski(k1_tops_1(sK2,X1),X1) ) ),
    inference(resolution,[],[f48,f43])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f66,plain,
    ( ~ v5_tops_1(sK4,sK2)
    | v5_tops_1(sK3,sK1) ),
    inference(resolution,[],[f40,f46])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | ~ v5_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f78,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_pre_topc(sK1,X0),sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(global_subsumption,[],[f42,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | v4_pre_topc(k2_pre_topc(sK1,X0),sK1) ) ),
    inference(resolution,[],[f57,f41])).

fof(f41,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

% (14244)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f42,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,
    ( ~ v5_tops_1(sK4,sK2)
    | ~ v4_tops_1(sK3,sK1)
    | ~ v4_pre_topc(sK3,sK1) ),
    inference(resolution,[],[f47,f40])).

fof(f47,plain,
    ( sP0(sK2,sK4)
    | ~ v4_pre_topc(sK3,sK1)
    | ~ v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f248,plain,
    ( v5_tops_1(sK4,sK2)
    | ~ v4_tops_1(sK4,sK2) ),
    inference(global_subsumption,[],[f45,f75,f245])).

fof(f245,plain,
    ( ~ r1_tarski(k1_tops_1(sK2,sK4),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v4_tops_1(sK4,sK2)
    | v5_tops_1(sK4,sK2) ),
    inference(resolution,[],[f243,f157])).

fof(f157,plain,
    ( ~ r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,sK4)),sK4)
    | ~ v4_tops_1(sK4,sK2)
    | v5_tops_1(sK4,sK2) ),
    inference(resolution,[],[f154,f130])).

fof(f130,plain,
    ( ~ r1_tarski(sK4,k2_pre_topc(sK2,k1_tops_1(sK2,sK4)))
    | ~ r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,sK4)),sK4)
    | v5_tops_1(sK4,sK2) ),
    inference(extensionality_resolution,[],[f61,f127])).

fof(f243,plain,(
    ! [X0] :
      ( r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,X0)),sK4)
      | ~ r1_tarski(k1_tops_1(sK2,X0),sK4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(global_subsumption,[],[f43,f241])).

fof(f241,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tops_1(sK2,X0),sK4)
      | r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,X0)),sK4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2) ) ),
    inference(resolution,[],[f239,f58])).

fof(f239,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r1_tarski(X0,sK4)
      | r1_tarski(k2_pre_topc(sK2,X0),sK4) ) ),
    inference(resolution,[],[f233,f62])).

fof(f233,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK3,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r1_tarski(X0,sK4)
      | r1_tarski(k2_pre_topc(sK2,X0),sK4) ) ),
    inference(resolution,[],[f232,f175])).

fof(f232,plain,
    ( v4_pre_topc(sK4,sK2)
    | ~ r1_tarski(sK3,sK3) ),
    inference(resolution,[],[f230,f205])).

fof(f205,plain,
    ( ~ v4_tops_1(sK3,sK1)
    | v4_pre_topc(sK4,sK2) ),
    inference(subsumption_resolution,[],[f69,f202])).

fof(f69,plain,
    ( ~ v4_tops_1(sK3,sK1)
    | ~ v4_pre_topc(sK3,sK1)
    | v4_pre_topc(sK4,sK2) ),
    inference(resolution,[],[f47,f38])).

fof(f206,plain,
    ( v4_tops_1(sK4,sK2)
    | ~ v4_tops_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f68,f202])).

fof(f68,plain,
    ( v4_tops_1(sK4,sK2)
    | ~ v4_tops_1(sK3,sK1)
    | ~ v4_pre_topc(sK3,sK1) ),
    inference(resolution,[],[f47,f39])).

fof(f230,plain,
    ( v4_tops_1(sK3,sK1)
    | ~ r1_tarski(sK3,sK3) ),
    inference(global_subsumption,[],[f73,f229])).

fof(f229,plain,
    ( ~ r1_tarski(sK3,sK3)
    | ~ r1_tarski(k1_tops_1(sK1,sK3),sK3)
    | v4_tops_1(sK3,sK1) ),
    inference(forward_demodulation,[],[f228,f192])).

fof(f228,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,sK3),sK3)
    | ~ r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))
    | v4_tops_1(sK3,sK1) ),
    inference(forward_demodulation,[],[f226,f204])).

fof(f204,plain,(
    sK3 = k2_pre_topc(sK1,sK3) ),
    inference(subsumption_resolution,[],[f87,f202])).

fof(f87,plain,
    ( ~ v4_pre_topc(sK3,sK1)
    | sK3 = k2_pre_topc(sK1,sK3) ),
    inference(resolution,[],[f85,f44])).

fof(f85,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | k2_pre_topc(sK1,X0) = X0 ) ),
    inference(resolution,[],[f49,f42])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f226,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))
    | v4_tops_1(sK3,sK1) ),
    inference(resolution,[],[f199,f44])).

fof(f199,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0)
      | ~ r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0)))
      | v4_tops_1(X0,sK1) ) ),
    inference(resolution,[],[f55,f42])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f73,plain,(
    r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
    inference(resolution,[],[f71,f44])).

fof(f71,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | r1_tarski(k1_tops_1(sK1,X0),X0) ) ),
    inference(resolution,[],[f48,f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:23:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (14256)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.49  % (14266)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.50  % (14248)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (14255)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.50  % (14246)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (14257)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (14256)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f254,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(resolution,[],[f253,f62])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(flattening,[],[f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.51  fof(f253,plain,(
% 0.20/0.51    ~r1_tarski(sK3,sK3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f230,f252])).
% 0.20/0.51  % (14258)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (14250)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.52  % (14269)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.52  % (14264)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.52  % (14253)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.52  % (14251)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (14261)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.52  % (14262)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.31/0.53  % (14245)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.31/0.53  % (14245)Refutation not found, incomplete strategy% (14245)------------------------------
% 1.31/0.53  % (14245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (14245)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.53  
% 1.31/0.53  % (14245)Memory used [KB]: 10618
% 1.31/0.53  % (14245)Time elapsed: 0.104 s
% 1.31/0.53  % (14245)------------------------------
% 1.31/0.53  % (14245)------------------------------
% 1.31/0.53  fof(f252,plain,(
% 1.31/0.53    ~v4_tops_1(sK3,sK1)),
% 1.31/0.53    inference(global_subsumption,[],[f206,f249])).
% 1.31/0.53  fof(f249,plain,(
% 1.31/0.53    ~v4_tops_1(sK4,sK2) | ~v4_tops_1(sK3,sK1)),
% 1.31/0.53    inference(resolution,[],[f248,f207])).
% 1.31/0.53  fof(f207,plain,(
% 1.31/0.53    ~v5_tops_1(sK4,sK2) | ~v4_tops_1(sK3,sK1)),
% 1.31/0.53    inference(subsumption_resolution,[],[f67,f202])).
% 1.31/0.53  fof(f202,plain,(
% 1.31/0.53    v4_pre_topc(sK3,sK1)),
% 1.31/0.53    inference(global_subsumption,[],[f44,f42,f201])).
% 1.31/0.53  fof(f201,plain,(
% 1.31/0.53    v4_pre_topc(sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 1.31/0.53    inference(resolution,[],[f198,f58])).
% 1.31/0.53  fof(f58,plain,(
% 1.31/0.53    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f23])).
% 1.31/0.53  fof(f23,plain,(
% 1.31/0.53    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.31/0.53    inference(flattening,[],[f22])).
% 1.31/0.53  fof(f22,plain,(
% 1.31/0.53    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.31/0.53    inference(ennf_transformation,[],[f5])).
% 1.31/0.53  fof(f5,axiom,(
% 1.31/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 1.31/0.53  fof(f198,plain,(
% 1.31/0.53    ~m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v4_pre_topc(sK3,sK1)),
% 1.31/0.53    inference(superposition,[],[f78,f192])).
% 1.31/0.53  fof(f192,plain,(
% 1.31/0.53    sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),
% 1.31/0.53    inference(global_subsumption,[],[f45,f66,f75,f104,f107,f127,f189])).
% 1.31/0.53  fof(f189,plain,(
% 1.31/0.53    ~r1_tarski(k1_tops_1(sK2,sK4),sK4) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | sK4 = k2_pre_topc(sK2,k1_tops_1(sK2,sK4)) | ~v4_tops_1(sK4,sK2)),
% 1.31/0.53    inference(resolution,[],[f181,f158])).
% 1.31/0.53  fof(f158,plain,(
% 1.31/0.53    ~r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,sK4)),sK4) | sK4 = k2_pre_topc(sK2,k1_tops_1(sK2,sK4)) | ~v4_tops_1(sK4,sK2)),
% 1.31/0.53    inference(resolution,[],[f154,f61])).
% 1.31/0.53  fof(f61,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f37])).
% 1.31/0.53  fof(f154,plain,(
% 1.31/0.53    r1_tarski(sK4,k2_pre_topc(sK2,k1_tops_1(sK2,sK4))) | ~v4_tops_1(sK4,sK2)),
% 1.31/0.53    inference(resolution,[],[f146,f45])).
% 1.31/0.53  fof(f146,plain,(
% 1.31/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~v4_tops_1(X1,sK2) | r1_tarski(X1,k2_pre_topc(sK2,k1_tops_1(sK2,X1)))) )),
% 1.31/0.53    inference(resolution,[],[f54,f43])).
% 1.31/0.53  fof(f43,plain,(
% 1.31/0.53    l1_pre_topc(sK2)),
% 1.31/0.53    inference(cnf_transformation,[],[f32])).
% 1.31/0.53  fof(f32,plain,(
% 1.31/0.53    ((((((~v4_tops_1(sK3,sK1) | ~v4_pre_topc(sK3,sK1)) & v5_tops_1(sK3,sK1)) | sP0(sK2,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 1.31/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f31,f30,f29,f28])).
% 1.31/0.53  fof(f28,plain,(
% 1.31/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | sP0(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK1) | ~v4_pre_topc(X2,sK1)) & v5_tops_1(X2,sK1)) | sP0(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 1.31/0.53    introduced(choice_axiom,[])).
% 1.31/0.53  fof(f29,plain,(
% 1.31/0.53    ? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK1) | ~v4_pre_topc(X2,sK1)) & v5_tops_1(X2,sK1)) | sP0(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK1) | ~v4_pre_topc(X2,sK1)) & v5_tops_1(X2,sK1)) | sP0(sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK2))),
% 1.31/0.53    introduced(choice_axiom,[])).
% 1.31/0.53  fof(f30,plain,(
% 1.31/0.53    ? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK1) | ~v4_pre_topc(X2,sK1)) & v5_tops_1(X2,sK1)) | sP0(sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) => (? [X3] : ((((~v4_tops_1(sK3,sK1) | ~v4_pre_topc(sK3,sK1)) & v5_tops_1(sK3,sK1)) | sP0(sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.31/0.53    introduced(choice_axiom,[])).
% 1.31/0.53  fof(f31,plain,(
% 1.31/0.53    ? [X3] : ((((~v4_tops_1(sK3,sK1) | ~v4_pre_topc(sK3,sK1)) & v5_tops_1(sK3,sK1)) | sP0(sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) => ((((~v4_tops_1(sK3,sK1) | ~v4_pre_topc(sK3,sK1)) & v5_tops_1(sK3,sK1)) | sP0(sK2,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))))),
% 1.31/0.53    introduced(choice_axiom,[])).
% 1.31/0.53  fof(f25,plain,(
% 1.31/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | sP0(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.31/0.53    inference(definition_folding,[],[f12,f24])).
% 1.31/0.53  fof(f24,plain,(
% 1.31/0.53    ! [X1,X3] : ((~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) | ~sP0(X1,X3))),
% 1.31/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.31/0.53  fof(f12,plain,(
% 1.31/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.31/0.53    inference(flattening,[],[f11])).
% 1.31/0.53  fof(f11,plain,(
% 1.31/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & (v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.31/0.53    inference(ennf_transformation,[],[f10])).
% 1.31/0.53  fof(f10,negated_conjecture,(
% 1.31/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v5_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v4_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) => v5_tops_1(X3,X1)))))))),
% 1.31/0.53    inference(negated_conjecture,[],[f9])).
% 1.31/0.53  fof(f9,conjecture,(
% 1.31/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v5_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v4_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) => v5_tops_1(X3,X1)))))))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tops_1)).
% 1.31/0.53  fof(f54,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))) )),
% 1.31/0.53    inference(cnf_transformation,[],[f35])).
% 1.31/0.53  fof(f35,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.31/0.53    inference(flattening,[],[f34])).
% 1.31/0.53  fof(f34,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.31/0.53    inference(nnf_transformation,[],[f17])).
% 1.31/0.53  fof(f17,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.31/0.53    inference(ennf_transformation,[],[f3])).
% 1.31/0.53  fof(f3,axiom,(
% 1.31/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).
% 1.31/0.53  fof(f181,plain,(
% 1.31/0.53    ( ! [X0] : (r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,X0)),sK4) | ~r1_tarski(k1_tops_1(sK2,X0),sK4) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.31/0.53    inference(global_subsumption,[],[f43,f180])).
% 1.31/0.53  fof(f180,plain,(
% 1.31/0.53    ( ! [X0] : (~r1_tarski(k1_tops_1(sK2,X0),sK4) | r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,X0)),sK4) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)) )),
% 1.31/0.53    inference(resolution,[],[f178,f58])).
% 1.31/0.53  fof(f178,plain,(
% 1.31/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(X0,sK4) | r1_tarski(k2_pre_topc(sK2,X0),sK4) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) )),
% 1.31/0.53    inference(resolution,[],[f175,f108])).
% 1.31/0.53  fof(f108,plain,(
% 1.31/0.53    v4_pre_topc(sK4,sK2) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),
% 1.31/0.53    inference(resolution,[],[f104,f64])).
% 1.31/0.53  fof(f64,plain,(
% 1.31/0.53    v5_tops_1(sK3,sK1) | v4_pre_topc(sK4,sK2)),
% 1.31/0.53    inference(resolution,[],[f38,f46])).
% 1.31/0.53  fof(f46,plain,(
% 1.31/0.53    sP0(sK2,sK4) | v5_tops_1(sK3,sK1)),
% 1.31/0.53    inference(cnf_transformation,[],[f32])).
% 1.31/0.53  fof(f38,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~sP0(X0,X1) | v4_pre_topc(X1,X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f27])).
% 1.31/0.53  fof(f27,plain,(
% 1.31/0.53    ! [X0,X1] : ((~v5_tops_1(X1,X0) & v4_tops_1(X1,X0) & v4_pre_topc(X1,X0)) | ~sP0(X0,X1))),
% 1.31/0.53    inference(rectify,[],[f26])).
% 1.31/0.53  fof(f26,plain,(
% 1.31/0.53    ! [X1,X3] : ((~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) | ~sP0(X1,X3))),
% 1.31/0.53    inference(nnf_transformation,[],[f24])).
% 1.31/0.53  fof(f175,plain,(
% 1.31/0.53    ( ! [X0] : (~v4_pre_topc(sK4,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(X0,sK4) | r1_tarski(k2_pre_topc(sK2,X0),sK4)) )),
% 1.31/0.53    inference(resolution,[],[f166,f45])).
% 1.31/0.53  fof(f166,plain,(
% 1.31/0.53    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | ~v4_pre_topc(X3,sK2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(X2,X3) | r1_tarski(k2_pre_topc(sK2,X2),X3)) )),
% 1.31/0.53    inference(resolution,[],[f56,f43])).
% 1.31/0.53  fof(f56,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k2_pre_topc(X0,X2),X1)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f19])).
% 1.31/0.53  fof(f19,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X2),X1) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.31/0.53    inference(flattening,[],[f18])).
% 1.31/0.53  fof(f18,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X2),X1) | (~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.31/0.53    inference(ennf_transformation,[],[f7])).
% 1.31/0.53  fof(f7,axiom,(
% 1.31/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X2,X1) & v4_pre_topc(X1,X0)) => r1_tarski(k2_pre_topc(X0,X2),X1)))))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_1)).
% 1.31/0.53  fof(f127,plain,(
% 1.31/0.53    sK4 != k2_pre_topc(sK2,k1_tops_1(sK2,sK4)) | v5_tops_1(sK4,sK2)),
% 1.31/0.53    inference(resolution,[],[f118,f45])).
% 1.31/0.53  fof(f118,plain,(
% 1.31/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | k2_pre_topc(sK2,k1_tops_1(sK2,X1)) != X1 | v5_tops_1(X1,sK2)) )),
% 1.31/0.53    inference(resolution,[],[f52,f43])).
% 1.31/0.53  fof(f52,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v5_tops_1(X1,X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f33])).
% 1.31/0.53  fof(f33,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.31/0.53    inference(nnf_transformation,[],[f16])).
% 1.31/0.53  fof(f16,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.31/0.53    inference(ennf_transformation,[],[f4])).
% 1.31/0.53  fof(f4,axiom,(
% 1.31/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).
% 1.31/0.53  fof(f107,plain,(
% 1.31/0.53    v4_tops_1(sK4,sK2) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),
% 1.31/0.53    inference(resolution,[],[f104,f65])).
% 1.31/0.53  fof(f65,plain,(
% 1.31/0.53    v5_tops_1(sK3,sK1) | v4_tops_1(sK4,sK2)),
% 1.31/0.53    inference(resolution,[],[f39,f46])).
% 1.31/0.53  fof(f39,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~sP0(X0,X1) | v4_tops_1(X1,X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f27])).
% 1.31/0.53  fof(f104,plain,(
% 1.31/0.53    ~v5_tops_1(sK3,sK1) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),
% 1.31/0.53    inference(resolution,[],[f102,f44])).
% 1.31/0.53  fof(f102,plain,(
% 1.31/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v5_tops_1(X0,sK1) | k2_pre_topc(sK1,k1_tops_1(sK1,X0)) = X0) )),
% 1.31/0.53    inference(resolution,[],[f51,f42])).
% 1.31/0.53  fof(f51,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) )),
% 1.31/0.53    inference(cnf_transformation,[],[f33])).
% 1.31/0.53  fof(f75,plain,(
% 1.31/0.53    r1_tarski(k1_tops_1(sK2,sK4),sK4)),
% 1.31/0.53    inference(resolution,[],[f72,f45])).
% 1.31/0.53  fof(f72,plain,(
% 1.31/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | r1_tarski(k1_tops_1(sK2,X1),X1)) )),
% 1.31/0.53    inference(resolution,[],[f48,f43])).
% 1.31/0.53  fof(f48,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f13])).
% 1.31/0.53  fof(f13,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.31/0.53    inference(ennf_transformation,[],[f8])).
% 1.31/0.53  fof(f8,axiom,(
% 1.31/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 1.31/0.53  fof(f66,plain,(
% 1.31/0.53    ~v5_tops_1(sK4,sK2) | v5_tops_1(sK3,sK1)),
% 1.31/0.53    inference(resolution,[],[f40,f46])).
% 1.31/0.53  fof(f40,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~sP0(X0,X1) | ~v5_tops_1(X1,X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f27])).
% 1.31/0.53  fof(f45,plain,(
% 1.31/0.53    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.31/0.53    inference(cnf_transformation,[],[f32])).
% 1.31/0.53  fof(f78,plain,(
% 1.31/0.53    ( ! [X0] : (v4_pre_topc(k2_pre_topc(sK1,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 1.31/0.53    inference(global_subsumption,[],[f42,f77])).
% 1.31/0.53  fof(f77,plain,(
% 1.31/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | v4_pre_topc(k2_pre_topc(sK1,X0),sK1)) )),
% 1.31/0.53    inference(resolution,[],[f57,f41])).
% 1.31/0.53  fof(f41,plain,(
% 1.31/0.53    v2_pre_topc(sK1)),
% 1.31/0.53    inference(cnf_transformation,[],[f32])).
% 1.31/0.53  fof(f57,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v4_pre_topc(k2_pre_topc(X0,X1),X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f21])).
% 1.31/0.53  fof(f21,plain,(
% 1.31/0.53    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.31/0.53    inference(flattening,[],[f20])).
% 1.31/0.53  fof(f20,plain,(
% 1.31/0.53    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.31/0.53    inference(ennf_transformation,[],[f6])).
% 1.31/0.53  % (14244)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.31/0.53  fof(f6,axiom,(
% 1.31/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 1.31/0.53  fof(f42,plain,(
% 1.31/0.53    l1_pre_topc(sK1)),
% 1.31/0.53    inference(cnf_transformation,[],[f32])).
% 1.31/0.53  fof(f44,plain,(
% 1.31/0.53    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.31/0.53    inference(cnf_transformation,[],[f32])).
% 1.31/0.53  fof(f67,plain,(
% 1.31/0.53    ~v5_tops_1(sK4,sK2) | ~v4_tops_1(sK3,sK1) | ~v4_pre_topc(sK3,sK1)),
% 1.31/0.53    inference(resolution,[],[f47,f40])).
% 1.31/0.53  fof(f47,plain,(
% 1.31/0.53    sP0(sK2,sK4) | ~v4_pre_topc(sK3,sK1) | ~v4_tops_1(sK3,sK1)),
% 1.31/0.53    inference(cnf_transformation,[],[f32])).
% 1.31/0.53  fof(f248,plain,(
% 1.31/0.53    v5_tops_1(sK4,sK2) | ~v4_tops_1(sK4,sK2)),
% 1.31/0.53    inference(global_subsumption,[],[f45,f75,f245])).
% 1.31/0.53  fof(f245,plain,(
% 1.31/0.53    ~r1_tarski(k1_tops_1(sK2,sK4),sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~v4_tops_1(sK4,sK2) | v5_tops_1(sK4,sK2)),
% 1.31/0.53    inference(resolution,[],[f243,f157])).
% 1.31/0.53  fof(f157,plain,(
% 1.31/0.53    ~r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,sK4)),sK4) | ~v4_tops_1(sK4,sK2) | v5_tops_1(sK4,sK2)),
% 1.31/0.53    inference(resolution,[],[f154,f130])).
% 1.31/0.53  fof(f130,plain,(
% 1.31/0.53    ~r1_tarski(sK4,k2_pre_topc(sK2,k1_tops_1(sK2,sK4))) | ~r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,sK4)),sK4) | v5_tops_1(sK4,sK2)),
% 1.31/0.53    inference(extensionality_resolution,[],[f61,f127])).
% 1.31/0.53  fof(f243,plain,(
% 1.31/0.53    ( ! [X0] : (r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,X0)),sK4) | ~r1_tarski(k1_tops_1(sK2,X0),sK4) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.31/0.53    inference(global_subsumption,[],[f43,f241])).
% 1.31/0.53  fof(f241,plain,(
% 1.31/0.53    ( ! [X0] : (~r1_tarski(k1_tops_1(sK2,X0),sK4) | r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,X0)),sK4) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)) )),
% 1.31/0.53    inference(resolution,[],[f239,f58])).
% 1.31/0.53  fof(f239,plain,(
% 1.31/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(X0,sK4) | r1_tarski(k2_pre_topc(sK2,X0),sK4)) )),
% 1.31/0.53    inference(resolution,[],[f233,f62])).
% 1.31/0.53  fof(f233,plain,(
% 1.31/0.53    ( ! [X0] : (~r1_tarski(sK3,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(X0,sK4) | r1_tarski(k2_pre_topc(sK2,X0),sK4)) )),
% 1.31/0.53    inference(resolution,[],[f232,f175])).
% 1.31/0.53  fof(f232,plain,(
% 1.31/0.53    v4_pre_topc(sK4,sK2) | ~r1_tarski(sK3,sK3)),
% 1.31/0.53    inference(resolution,[],[f230,f205])).
% 1.31/0.53  fof(f205,plain,(
% 1.31/0.53    ~v4_tops_1(sK3,sK1) | v4_pre_topc(sK4,sK2)),
% 1.31/0.53    inference(subsumption_resolution,[],[f69,f202])).
% 1.31/0.53  fof(f69,plain,(
% 1.31/0.53    ~v4_tops_1(sK3,sK1) | ~v4_pre_topc(sK3,sK1) | v4_pre_topc(sK4,sK2)),
% 1.31/0.53    inference(resolution,[],[f47,f38])).
% 1.31/0.53  fof(f206,plain,(
% 1.31/0.53    v4_tops_1(sK4,sK2) | ~v4_tops_1(sK3,sK1)),
% 1.31/0.53    inference(subsumption_resolution,[],[f68,f202])).
% 1.31/0.53  fof(f68,plain,(
% 1.31/0.53    v4_tops_1(sK4,sK2) | ~v4_tops_1(sK3,sK1) | ~v4_pre_topc(sK3,sK1)),
% 1.31/0.53    inference(resolution,[],[f47,f39])).
% 1.31/0.53  fof(f230,plain,(
% 1.31/0.53    v4_tops_1(sK3,sK1) | ~r1_tarski(sK3,sK3)),
% 1.31/0.53    inference(global_subsumption,[],[f73,f229])).
% 1.31/0.53  fof(f229,plain,(
% 1.31/0.53    ~r1_tarski(sK3,sK3) | ~r1_tarski(k1_tops_1(sK1,sK3),sK3) | v4_tops_1(sK3,sK1)),
% 1.31/0.53    inference(forward_demodulation,[],[f228,f192])).
% 1.31/0.53  fof(f228,plain,(
% 1.31/0.53    ~r1_tarski(k1_tops_1(sK1,sK3),sK3) | ~r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) | v4_tops_1(sK3,sK1)),
% 1.31/0.53    inference(forward_demodulation,[],[f226,f204])).
% 1.31/0.53  fof(f204,plain,(
% 1.31/0.53    sK3 = k2_pre_topc(sK1,sK3)),
% 1.31/0.53    inference(subsumption_resolution,[],[f87,f202])).
% 1.31/0.53  fof(f87,plain,(
% 1.31/0.53    ~v4_pre_topc(sK3,sK1) | sK3 = k2_pre_topc(sK1,sK3)),
% 1.31/0.53    inference(resolution,[],[f85,f44])).
% 1.31/0.53  fof(f85,plain,(
% 1.31/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | k2_pre_topc(sK1,X0) = X0) )),
% 1.31/0.53    inference(resolution,[],[f49,f42])).
% 1.31/0.53  fof(f49,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) )),
% 1.31/0.53    inference(cnf_transformation,[],[f15])).
% 1.31/0.53  fof(f15,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.31/0.53    inference(flattening,[],[f14])).
% 1.31/0.53  fof(f14,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.31/0.53    inference(ennf_transformation,[],[f2])).
% 1.31/0.53  fof(f2,axiom,(
% 1.31/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.31/0.53  fof(f226,plain,(
% 1.31/0.53    ~r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) | ~r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) | v4_tops_1(sK3,sK1)),
% 1.31/0.53    inference(resolution,[],[f199,f44])).
% 1.31/0.53  fof(f199,plain,(
% 1.31/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) | ~r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) | v4_tops_1(X0,sK1)) )),
% 1.31/0.53    inference(resolution,[],[f55,f42])).
% 1.31/0.53  fof(f55,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_tops_1(X1,X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f35])).
% 1.31/0.53  fof(f73,plain,(
% 1.31/0.53    r1_tarski(k1_tops_1(sK1,sK3),sK3)),
% 1.31/0.53    inference(resolution,[],[f71,f44])).
% 1.31/0.53  fof(f71,plain,(
% 1.31/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tarski(k1_tops_1(sK1,X0),X0)) )),
% 1.31/0.53    inference(resolution,[],[f48,f42])).
% 1.31/0.53  % SZS output end Proof for theBenchmark
% 1.31/0.53  % (14256)------------------------------
% 1.31/0.53  % (14256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (14256)Termination reason: Refutation
% 1.31/0.53  
% 1.31/0.53  % (14256)Memory used [KB]: 6524
% 1.31/0.53  % (14256)Time elapsed: 0.110 s
% 1.31/0.53  % (14256)------------------------------
% 1.31/0.53  % (14256)------------------------------
% 1.31/0.53  % (14243)Success in time 0.176 s
%------------------------------------------------------------------------------
