%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:46 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 176 expanded)
%              Number of leaves         :   19 (  45 expanded)
%              Depth                    :   23
%              Number of atoms          :  397 ( 943 expanded)
%              Number of equality atoms :   33 (  94 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f194,plain,(
    $false ),
    inference(subsumption_resolution,[],[f193,f48])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_1)).

fof(f193,plain,(
    ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f190,f47])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f190,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f187,f61])).

fof(f61,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK4(X0),sK5(X0)),u1_pre_topc(X0))
            & r2_hidden(sK5(X0),u1_pre_topc(X0))
            & r2_hidden(sK4(X0),u1_pre_topc(X0))
            & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))
            & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) )
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK6(X0)),u1_pre_topc(X0))
            & r1_tarski(sK6(X0),u1_pre_topc(X0))
            & m1_subset_1(sK6(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0))
                    | ~ r2_hidden(X5,u1_pre_topc(X0))
                    | ~ r2_hidden(X4,u1_pre_topc(X0))
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            & ! [X6] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0))
                | ~ r1_tarski(X6,u1_pre_topc(X0))
                | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f37,f40,f39,f38])).

% (23933)Refutation not found, incomplete strategy% (23933)------------------------------
% (23933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23933)Termination reason: Refutation not found, incomplete strategy

% (23933)Memory used [KB]: 10618
% (23933)Time elapsed: 0.125 s
% (23933)------------------------------
% (23933)------------------------------
% (23922)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% (23931)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (23949)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (23950)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (23941)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (23948)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (23929)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (23937)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (23924)Refutation not found, incomplete strategy% (23924)------------------------------
% (23924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23924)Termination reason: Refutation not found, incomplete strategy

% (23924)Memory used [KB]: 10746
% (23924)Time elapsed: 0.135 s
% (23924)------------------------------
% (23924)------------------------------
% (23942)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (23942)Refutation not found, incomplete strategy% (23942)------------------------------
% (23942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              & r2_hidden(X2,u1_pre_topc(X0))
              & r2_hidden(X1,u1_pre_topc(X0))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK4(X0),X2),u1_pre_topc(X0))
            & r2_hidden(X2,u1_pre_topc(X0))
            & r2_hidden(sK4(X0),u1_pre_topc(X0))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK4(X0),X2),u1_pre_topc(X0))
          & r2_hidden(X2,u1_pre_topc(X0))
          & r2_hidden(sK4(X0),u1_pre_topc(X0))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK4(X0),sK5(X0)),u1_pre_topc(X0))
        & r2_hidden(sK5(X0),u1_pre_topc(X0))
        & r2_hidden(sK4(X0),u1_pre_topc(X0))
        & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
          & r1_tarski(X3,u1_pre_topc(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK6(X0)),u1_pre_topc(X0))
        & r1_tarski(sK6(X0),u1_pre_topc(X0))
        & m1_subset_1(sK6(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  & r2_hidden(X2,u1_pre_topc(X0))
                  & r2_hidden(X1,u1_pre_topc(X0))
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0))
                    | ~ r2_hidden(X5,u1_pre_topc(X0))
                    | ~ r2_hidden(X4,u1_pre_topc(X0))
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            & ! [X6] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0))
                | ~ r1_tarski(X6,u1_pre_topc(X0))
                | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  & r2_hidden(X2,u1_pre_topc(X0))
                  & r2_hidden(X1,u1_pre_topc(X0))
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( ! [X1] :
                ( ! [X2] :
                    ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                    | ~ r2_hidden(X2,u1_pre_topc(X0))
                    | ~ r2_hidden(X1,u1_pre_topc(X0))
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  & r2_hidden(X2,u1_pre_topc(X0))
                  & r2_hidden(X1,u1_pre_topc(X0))
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( ! [X1] :
                ( ! [X2] :
                    ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                    | ~ r2_hidden(X2,u1_pre_topc(X0))
                    | ~ r2_hidden(X1,u1_pre_topc(X0))
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f187,plain,(
    ! [X0] : ~ r2_hidden(X0,u1_pre_topc(sK0)) ),
    inference(resolution,[],[f186,f90])).

fof(f90,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f186,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,u1_pre_topc(sK0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f185,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f185,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK0)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f184,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f184,plain,(
    v1_xboole_0(u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f183,f48])).

fof(f183,plain,
    ( v1_xboole_0(u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f180,f47])).

fof(f180,plain,
    ( v1_xboole_0(u1_pre_topc(sK0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f179,f61])).

fof(f179,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | v1_xboole_0(u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f177,f49])).

fof(f49,plain,(
    u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f177,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_struct_0(sK0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    | v1_xboole_0(u1_pre_topc(sK0)) ),
    inference(superposition,[],[f59,f161])).

fof(f161,plain,(
    u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f102,f160])).

fof(f160,plain,(
    r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f159,f48])).

fof(f159,plain,
    ( r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f140,f47])).

fof(f140,plain,(
    ! [X11] :
      ( ~ v2_pre_topc(X11)
      | r1_tarski(u1_struct_0(X11),k3_tarski(u1_pre_topc(X11)))
      | ~ l1_pre_topc(X11) ) ),
    inference(resolution,[],[f135,f61])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1))
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(resolution,[],[f107,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f43,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(X2,k3_tarski(X1)),X0)
      | ~ r2_hidden(X0,X1)
      | r1_tarski(X2,k3_tarski(X1)) ) ),
    inference(resolution,[],[f87,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f87,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK1(X0,X1),X3) )
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( ( r2_hidden(sK2(X0,X1),X0)
              & r2_hidden(sK1(X0,X1),sK2(X0,X1)) )
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK3(X0,X5),X0)
                & r2_hidden(X5,sK3(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f28,f31,f30,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK1(X0,X1),X3) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK1(X0,X1),X4) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK1(X0,X1),X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f102,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0)))
    | u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0)) ),
    inference(resolution,[],[f101,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f101,plain,(
    r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f100,f60])).

fof(f60,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f100,plain,(
    r1_tarski(k3_tarski(u1_pre_topc(sK0)),k3_tarski(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f98,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f98,plain,(
    r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f97,f48])).

fof(f97,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | r1_tarski(u1_pre_topc(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(resolution,[],[f79,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f79,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f59,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_tarski(X0),X0)
      | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:05:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (23943)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.50  % (23943)Refutation not found, incomplete strategy% (23943)------------------------------
% 0.20/0.50  % (23943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (23951)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.51  % (23935)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (23943)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (23943)Memory used [KB]: 1791
% 0.20/0.51  % (23943)Time elapsed: 0.095 s
% 0.20/0.51  % (23943)------------------------------
% 0.20/0.51  % (23943)------------------------------
% 0.20/0.51  % (23934)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (23932)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (23933)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (23923)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (23944)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.24/0.52  % (23928)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.24/0.53  % (23925)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.24/0.53  % (23924)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.24/0.53  % (23938)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.24/0.53  % (23936)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.24/0.53  % (23930)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.24/0.53  % (23927)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.24/0.53  % (23926)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.24/0.53  % (23939)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.24/0.53  % (23945)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.24/0.53  % (23940)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.24/0.53  % (23947)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.24/0.53  % (23932)Refutation not found, incomplete strategy% (23932)------------------------------
% 1.24/0.53  % (23932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (23932)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.53  
% 1.24/0.53  % (23932)Memory used [KB]: 10618
% 1.24/0.53  % (23932)Time elapsed: 0.125 s
% 1.24/0.53  % (23932)------------------------------
% 1.24/0.53  % (23932)------------------------------
% 1.24/0.54  % (23927)Refutation found. Thanks to Tanya!
% 1.24/0.54  % SZS status Theorem for theBenchmark
% 1.24/0.54  % SZS output start Proof for theBenchmark
% 1.24/0.54  fof(f194,plain,(
% 1.24/0.54    $false),
% 1.24/0.54    inference(subsumption_resolution,[],[f193,f48])).
% 1.24/0.54  fof(f48,plain,(
% 1.24/0.54    l1_pre_topc(sK0)),
% 1.24/0.54    inference(cnf_transformation,[],[f26])).
% 1.24/0.54  fof(f26,plain,(
% 1.24/0.54    u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.24/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f25])).
% 1.24/0.54  fof(f25,plain,(
% 1.24/0.54    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.24/0.54    introduced(choice_axiom,[])).
% 1.24/0.54  fof(f16,plain,(
% 1.24/0.54    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.24/0.54    inference(flattening,[],[f15])).
% 1.24/0.54  fof(f15,plain,(
% 1.24/0.54    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.24/0.54    inference(ennf_transformation,[],[f14])).
% 1.24/0.54  fof(f14,plain,(
% 1.24/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 1.24/0.54    inference(pure_predicate_removal,[],[f12])).
% 1.24/0.54  fof(f12,negated_conjecture,(
% 1.24/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 1.24/0.54    inference(negated_conjecture,[],[f11])).
% 1.24/0.54  fof(f11,conjecture,(
% 1.24/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_1)).
% 1.24/0.54  fof(f193,plain,(
% 1.24/0.54    ~l1_pre_topc(sK0)),
% 1.24/0.54    inference(subsumption_resolution,[],[f190,f47])).
% 1.24/0.54  fof(f47,plain,(
% 1.24/0.54    v2_pre_topc(sK0)),
% 1.24/0.54    inference(cnf_transformation,[],[f26])).
% 1.24/0.54  fof(f190,plain,(
% 1.24/0.54    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0)),
% 1.24/0.54    inference(resolution,[],[f187,f61])).
% 1.24/0.54  fof(f61,plain,(
% 1.24/0.54    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f41])).
% 1.24/0.54  fof(f41,plain,(
% 1.24/0.54    ! [X0] : (((v2_pre_topc(X0) | ((~r2_hidden(k9_subset_1(u1_struct_0(X0),sK4(X0),sK5(X0)),u1_pre_topc(X0)) & r2_hidden(sK5(X0),u1_pre_topc(X0)) & r2_hidden(sK4(X0),u1_pre_topc(X0)) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK6(X0)),u1_pre_topc(X0)) & r1_tarski(sK6(X0),u1_pre_topc(X0)) & m1_subset_1(sK6(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X4] : (! [X5] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0)) | ~r2_hidden(X5,u1_pre_topc(X0)) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X6] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0)) | ~r1_tarski(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 1.24/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f37,f40,f39,f38])).
% 1.24/0.54  % (23933)Refutation not found, incomplete strategy% (23933)------------------------------
% 1.24/0.54  % (23933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (23933)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (23933)Memory used [KB]: 10618
% 1.24/0.54  % (23933)Time elapsed: 0.125 s
% 1.24/0.54  % (23933)------------------------------
% 1.24/0.54  % (23933)------------------------------
% 1.24/0.54  % (23922)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.24/0.54  % (23931)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.24/0.54  % (23949)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.44/0.54  % (23950)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.44/0.55  % (23941)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.44/0.55  % (23948)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.44/0.55  % (23929)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.44/0.55  % (23937)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.44/0.55  % (23924)Refutation not found, incomplete strategy% (23924)------------------------------
% 1.44/0.55  % (23924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (23924)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (23924)Memory used [KB]: 10746
% 1.44/0.55  % (23924)Time elapsed: 0.135 s
% 1.44/0.55  % (23924)------------------------------
% 1.44/0.55  % (23924)------------------------------
% 1.44/0.55  % (23942)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.44/0.55  % (23942)Refutation not found, incomplete strategy% (23942)------------------------------
% 1.44/0.55  % (23942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  fof(f38,plain,(
% 1.44/0.55    ! [X0] : (? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK4(X0),X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(sK4(X0),u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.44/0.55    introduced(choice_axiom,[])).
% 1.44/0.55  fof(f39,plain,(
% 1.44/0.55    ! [X0] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK4(X0),X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(sK4(X0),u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK4(X0),sK5(X0)),u1_pre_topc(X0)) & r2_hidden(sK5(X0),u1_pre_topc(X0)) & r2_hidden(sK4(X0),u1_pre_topc(X0)) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.44/0.55    introduced(choice_axiom,[])).
% 1.44/0.55  fof(f40,plain,(
% 1.44/0.55    ! [X0] : (? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK6(X0)),u1_pre_topc(X0)) & r1_tarski(sK6(X0),u1_pre_topc(X0)) & m1_subset_1(sK6(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.44/0.55    introduced(choice_axiom,[])).
% 1.44/0.55  fof(f37,plain,(
% 1.44/0.55    ! [X0] : (((v2_pre_topc(X0) | ? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X4] : (! [X5] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0)) | ~r2_hidden(X5,u1_pre_topc(X0)) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X6] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0)) | ~r1_tarski(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 1.44/0.55    inference(rectify,[],[f36])).
% 1.44/0.55  fof(f36,plain,(
% 1.44/0.55    ! [X0] : (((v2_pre_topc(X0) | ? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 1.44/0.55    inference(flattening,[],[f35])).
% 1.44/0.55  fof(f35,plain,(
% 1.44/0.55    ! [X0] : (((v2_pre_topc(X0) | (? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 1.44/0.55    inference(nnf_transformation,[],[f20])).
% 1.44/0.55  fof(f20,plain,(
% 1.44/0.55    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.44/0.55    inference(flattening,[],[f19])).
% 1.44/0.55  fof(f19,plain,(
% 1.44/0.55    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.44/0.55    inference(ennf_transformation,[],[f13])).
% 1.44/0.55  fof(f13,plain,(
% 1.44/0.55    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.44/0.55    inference(rectify,[],[f8])).
% 1.44/0.55  fof(f8,axiom,(
% 1.44/0.55    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).
% 1.44/0.55  fof(f187,plain,(
% 1.44/0.55    ( ! [X0] : (~r2_hidden(X0,u1_pre_topc(sK0))) )),
% 1.44/0.55    inference(resolution,[],[f186,f90])).
% 1.44/0.55  fof(f90,plain,(
% 1.44/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.44/0.55    inference(equality_resolution,[],[f57])).
% 1.44/0.55  fof(f57,plain,(
% 1.44/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.44/0.55    inference(cnf_transformation,[],[f34])).
% 1.44/0.55  fof(f34,plain,(
% 1.44/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.44/0.55    inference(flattening,[],[f33])).
% 1.44/0.55  fof(f33,plain,(
% 1.44/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.44/0.55    inference(nnf_transformation,[],[f2])).
% 1.44/0.55  fof(f2,axiom,(
% 1.44/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.44/0.55  fof(f186,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~r1_tarski(X1,u1_pre_topc(sK0)) | ~r2_hidden(X0,X1)) )),
% 1.44/0.55    inference(resolution,[],[f185,f86])).
% 1.44/0.55  fof(f86,plain,(
% 1.44/0.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f46])).
% 1.44/0.55  fof(f46,plain,(
% 1.44/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.44/0.55    inference(nnf_transformation,[],[f6])).
% 1.44/0.55  fof(f6,axiom,(
% 1.44/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.44/0.55  fof(f185,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK0))) | ~r2_hidden(X1,X0)) )),
% 1.44/0.55    inference(resolution,[],[f184,f80])).
% 1.44/0.55  fof(f80,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f22])).
% 1.44/0.55  fof(f22,plain,(
% 1.44/0.55    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.44/0.55    inference(ennf_transformation,[],[f7])).
% 1.44/0.55  fof(f7,axiom,(
% 1.44/0.55    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.44/0.55  fof(f184,plain,(
% 1.44/0.55    v1_xboole_0(u1_pre_topc(sK0))),
% 1.44/0.55    inference(subsumption_resolution,[],[f183,f48])).
% 1.44/0.55  fof(f183,plain,(
% 1.44/0.55    v1_xboole_0(u1_pre_topc(sK0)) | ~l1_pre_topc(sK0)),
% 1.44/0.55    inference(subsumption_resolution,[],[f180,f47])).
% 1.44/0.55  fof(f180,plain,(
% 1.44/0.55    v1_xboole_0(u1_pre_topc(sK0)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0)),
% 1.44/0.55    inference(resolution,[],[f179,f61])).
% 1.44/0.55  fof(f179,plain,(
% 1.44/0.55    ~r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) | v1_xboole_0(u1_pre_topc(sK0))),
% 1.44/0.55    inference(subsumption_resolution,[],[f177,f49])).
% 1.44/0.55  fof(f49,plain,(
% 1.44/0.55    u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))),
% 1.44/0.55    inference(cnf_transformation,[],[f26])).
% 1.44/0.55  fof(f177,plain,(
% 1.44/0.55    ~r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_struct_0(sK0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) | v1_xboole_0(u1_pre_topc(sK0))),
% 1.44/0.55    inference(superposition,[],[f59,f161])).
% 1.44/0.55  fof(f161,plain,(
% 1.44/0.55    u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0))),
% 1.44/0.55    inference(subsumption_resolution,[],[f102,f160])).
% 1.44/0.55  fof(f160,plain,(
% 1.44/0.55    r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0)))),
% 1.44/0.55    inference(subsumption_resolution,[],[f159,f48])).
% 1.44/0.55  fof(f159,plain,(
% 1.44/0.55    r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0))) | ~l1_pre_topc(sK0)),
% 1.44/0.55    inference(resolution,[],[f140,f47])).
% 1.44/0.55  fof(f140,plain,(
% 1.44/0.55    ( ! [X11] : (~v2_pre_topc(X11) | r1_tarski(u1_struct_0(X11),k3_tarski(u1_pre_topc(X11))) | ~l1_pre_topc(X11)) )),
% 1.44/0.55    inference(resolution,[],[f135,f61])).
% 1.44/0.55  fof(f135,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 1.44/0.55    inference(duplicate_literal_removal,[],[f129])).
% 1.44/0.55  fof(f129,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1)) | r1_tarski(X0,k3_tarski(X1))) )),
% 1.44/0.55    inference(resolution,[],[f107,f82])).
% 1.44/0.55  fof(f82,plain,(
% 1.44/0.55    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f45])).
% 1.44/0.55  fof(f45,plain,(
% 1.44/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.44/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f43,f44])).
% 1.44/0.55  fof(f44,plain,(
% 1.44/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 1.44/0.55    introduced(choice_axiom,[])).
% 1.44/0.55  fof(f43,plain,(
% 1.44/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.44/0.55    inference(rectify,[],[f42])).
% 1.44/0.55  fof(f42,plain,(
% 1.44/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.44/0.55    inference(nnf_transformation,[],[f23])).
% 1.44/0.55  fof(f23,plain,(
% 1.44/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.44/0.55    inference(ennf_transformation,[],[f1])).
% 1.44/0.55  fof(f1,axiom,(
% 1.44/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.44/0.55  fof(f107,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (~r2_hidden(sK7(X2,k3_tarski(X1)),X0) | ~r2_hidden(X0,X1) | r1_tarski(X2,k3_tarski(X1))) )),
% 1.44/0.55    inference(resolution,[],[f87,f83])).
% 1.44/0.55  fof(f83,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f45])).
% 1.44/0.55  fof(f87,plain,(
% 1.44/0.55    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 1.44/0.55    inference(equality_resolution,[],[f52])).
% 1.44/0.55  fof(f52,plain,(
% 1.44/0.55    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 1.44/0.55    inference(cnf_transformation,[],[f32])).
% 1.44/0.55  fof(f32,plain,(
% 1.44/0.55    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & ((r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),sK2(X0,X1))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 1.44/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f28,f31,f30,f29])).
% 1.44/0.55  fof(f29,plain,(
% 1.44/0.55    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK1(X0,X1),X4)) | r2_hidden(sK1(X0,X1),X1))))),
% 1.44/0.55    introduced(choice_axiom,[])).
% 1.44/0.55  fof(f30,plain,(
% 1.44/0.55    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK1(X0,X1),X4)) => (r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),sK2(X0,X1))))),
% 1.44/0.55    introduced(choice_axiom,[])).
% 1.44/0.55  fof(f31,plain,(
% 1.44/0.55    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))))),
% 1.44/0.55    introduced(choice_axiom,[])).
% 1.44/0.55  fof(f28,plain,(
% 1.44/0.55    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 1.44/0.55    inference(rectify,[],[f27])).
% 1.44/0.55  fof(f27,plain,(
% 1.44/0.55    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 1.44/0.55    inference(nnf_transformation,[],[f3])).
% 1.44/0.55  fof(f3,axiom,(
% 1.44/0.55    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 1.44/0.55  fof(f102,plain,(
% 1.44/0.55    ~r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0))) | u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0))),
% 1.44/0.55    inference(resolution,[],[f101,f58])).
% 1.44/0.55  fof(f58,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.44/0.55    inference(cnf_transformation,[],[f34])).
% 1.44/0.55  fof(f101,plain,(
% 1.44/0.55    r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0))),
% 1.44/0.55    inference(forward_demodulation,[],[f100,f60])).
% 1.44/0.55  fof(f60,plain,(
% 1.44/0.55    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 1.44/0.55    inference(cnf_transformation,[],[f5])).
% 1.44/0.55  fof(f5,axiom,(
% 1.44/0.55    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 1.44/0.55  fof(f100,plain,(
% 1.44/0.55    r1_tarski(k3_tarski(u1_pre_topc(sK0)),k3_tarski(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.44/0.55    inference(resolution,[],[f98,f84])).
% 1.44/0.55  fof(f84,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k3_tarski(X0),k3_tarski(X1))) )),
% 1.44/0.55    inference(cnf_transformation,[],[f24])).
% 1.44/0.55  fof(f24,plain,(
% 1.44/0.55    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 1.44/0.55    inference(ennf_transformation,[],[f4])).
% 1.44/0.55  fof(f4,axiom,(
% 1.44/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 1.44/0.55  fof(f98,plain,(
% 1.44/0.55    r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.44/0.55    inference(resolution,[],[f97,f48])).
% 1.44/0.55  fof(f97,plain,(
% 1.44/0.55    ( ! [X0] : (~l1_pre_topc(X0) | r1_tarski(u1_pre_topc(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.44/0.55    inference(resolution,[],[f79,f85])).
% 1.44/0.55  fof(f85,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f46])).
% 1.44/0.55  fof(f79,plain,(
% 1.44/0.55    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f21])).
% 1.44/0.55  fof(f21,plain,(
% 1.44/0.55    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.44/0.55    inference(ennf_transformation,[],[f9])).
% 1.44/0.55  fof(f9,axiom,(
% 1.44/0.55    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 1.44/0.55  fof(f59,plain,(
% 1.44/0.55    ( ! [X0] : (~r2_hidden(k3_tarski(X0),X0) | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f18])).
% 1.44/0.55  fof(f18,plain,(
% 1.44/0.55    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 1.44/0.55    inference(flattening,[],[f17])).
% 1.44/0.55  fof(f17,plain,(
% 1.44/0.55    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 1.44/0.55    inference(ennf_transformation,[],[f10])).
% 1.44/0.55  fof(f10,axiom,(
% 1.44/0.55    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).
% 1.44/0.55  % SZS output end Proof for theBenchmark
% 1.44/0.55  % (23927)------------------------------
% 1.44/0.55  % (23927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (23927)Termination reason: Refutation
% 1.44/0.55  
% 1.44/0.55  % (23927)Memory used [KB]: 6396
% 1.44/0.55  % (23927)Time elapsed: 0.131 s
% 1.44/0.55  % (23927)------------------------------
% 1.44/0.55  % (23927)------------------------------
% 1.44/0.56  % (23921)Success in time 0.198 s
%------------------------------------------------------------------------------
