%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:16 EST 2020

% Result     : Theorem 1.89s
% Output     : Refutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :  112 (1423 expanded)
%              Number of leaves         :   16 ( 417 expanded)
%              Depth                    :   23
%              Number of atoms          :  424 (14080 expanded)
%              Number of equality atoms :   26 (  26 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1223,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1199,f903])).

fof(f903,plain,(
    ~ r1_tarski(sK3,k1_tops_1(sK0,sK2)) ),
    inference(superposition,[],[f889,f630])).

fof(f630,plain,(
    sK3 = k2_xboole_0(k2_tarski(sK1,sK1),sK3) ),
    inference(resolution,[],[f625,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f625,plain,(
    r1_tarski(k2_tarski(sK1,sK1),sK3) ),
    inference(subsumption_resolution,[],[f624,f618])).

% (28692)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f618,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | r1_tarski(k2_tarski(sK1,sK1),sK3) ),
    inference(duplicate_literal_removal,[],[f617])).

fof(f617,plain,
    ( r1_tarski(k2_tarski(sK1,sK1),sK3)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f150,f51])).

fof(f51,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f38,f37,f36])).

fof(f36,plain,
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

fof(f37,plain,
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

fof(f38,plain,
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

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f15])).

% (28696)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f150,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | r1_tarski(k2_tarski(sK1,X0),sK3)
      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ) ),
    inference(resolution,[],[f51,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f624,plain,
    ( r1_tarski(k2_tarski(sK1,sK1),sK3)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f623,f110])).

fof(f110,plain,(
    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f96,f46])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f96,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f47,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f623,plain,
    ( r1_tarski(k2_tarski(sK1,sK1),sK3)
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f622,f109])).

fof(f109,plain,(
    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f108,f45])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f108,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f95,f46])).

fof(f95,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f47,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f622,plain,
    ( r1_tarski(k2_tarski(sK1,sK1),sK3)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f619,f99])).

fof(f99,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f87,f46])).

fof(f87,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f47,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f619,plain,
    ( r1_tarski(k2_tarski(sK1,sK1),sK3)
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f618,f52])).

fof(f52,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | ~ r1_tarski(X3,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f889,plain,(
    ! [X2,X1] : ~ r1_tarski(k2_xboole_0(k2_tarski(sK1,X1),X2),k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f881,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f881,plain,(
    ! [X11] : ~ r1_tarski(k2_tarski(sK1,X11),k1_tops_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f880,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f880,plain,(
    ! [X11] :
      ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
      | ~ r1_tarski(k2_tarski(sK1,X11),k1_tops_1(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f879,f110])).

fof(f879,plain,(
    ! [X11] :
      ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
      | ~ r1_tarski(k2_tarski(sK1,X11),k1_tops_1(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f875,f109])).

fof(f875,plain,(
    ! [X11] :
      ( ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
      | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
      | ~ r1_tarski(k2_tarski(sK1,X11),k1_tops_1(sK0,sK2)) ) ),
    inference(resolution,[],[f186,f99])).

fof(f186,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,sK2)
      | ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
      | ~ r1_tarski(k2_tarski(sK1,X1),X0) ) ),
    inference(resolution,[],[f52,f69])).

fof(f1199,plain,(
    r1_tarski(sK3,k1_tops_1(sK0,sK2)) ),
    inference(backward_demodulation,[],[f923,f1168])).

fof(f1168,plain,(
    sK3 = k1_tops_1(sK0,sK3) ),
    inference(subsumption_resolution,[],[f1163,f890])).

fof(f890,plain,(
    ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(condensation,[],[f888])).

fof(f888,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tops_1(sK0,sK2))
      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ) ),
    inference(resolution,[],[f881,f71])).

fof(f1163,plain,
    ( sK3 = k1_tops_1(sK0,sK3)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f1040,f751])).

fof(f751,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f142,f191])).

fof(f191,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f190,f48])).

fof(f48,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f190,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f189,f110])).

fof(f189,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f188,f109])).

fof(f188,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f185,f99])).

fof(f185,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f52,f48])).

fof(f142,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f141,f46])).

fof(f141,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f49,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

fof(f49,plain,
    ( v3_pre_topc(sK3,sK0)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f39])).

fof(f1040,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0)
    | sK3 = k1_tops_1(sK0,sK3) ),
    inference(forward_demodulation,[],[f1039,f202])).

fof(f202,plain,(
    sK3 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) ),
    inference(resolution,[],[f191,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f1039,plain,
    ( k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3))
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0) ),
    inference(subsumption_resolution,[],[f1031,f203])).

fof(f203,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f191,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f1031,plain,
    ( k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3))
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f205,f78])).

fof(f78,plain,(
    ! [X2] :
      ( k2_pre_topc(sK0,X2) = X2
      | ~ v4_pre_topc(X2,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f46,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f205,plain,(
    k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) ),
    inference(subsumption_resolution,[],[f193,f46])).

fof(f193,plain,
    ( k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f191,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f923,plain,(
    r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f922,f191])).

fof(f922,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f921,f47])).

fof(f921,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f908,f46])).

fof(f908,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,sK3),k1_tops_1(X0,sK2)) ) ),
    inference(subsumption_resolution,[],[f149,f890])).

fof(f149,plain,(
    ! [X0] :
      ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
      | r1_tarski(k1_tops_1(X0,sK3),k1_tops_1(X0,sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f50,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f50,plain,
    ( r1_tarski(sK3,sK2)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:37:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (28679)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.54  % (28688)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.55  % (28685)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.55  % (28687)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.55  % (28682)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.56  % (28681)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.56  % (28689)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.56  % (28680)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.56  % (28697)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.57  % (28693)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.57  % (28690)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.58  % (28695)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.58  % (28683)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.58  % (28704)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.58  % (28684)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.58  % (28700)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.75/0.59  % (28702)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.75/0.59  % (28694)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.89/0.60  % (28698)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.89/0.60  % (28699)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.89/0.61  % (28686)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.89/0.62  % (28687)Refutation found. Thanks to Tanya!
% 1.89/0.62  % SZS status Theorem for theBenchmark
% 1.89/0.62  % (28703)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.89/0.62  % SZS output start Proof for theBenchmark
% 1.89/0.62  fof(f1223,plain,(
% 1.89/0.62    $false),
% 1.89/0.62    inference(subsumption_resolution,[],[f1199,f903])).
% 1.89/0.62  fof(f903,plain,(
% 1.89/0.62    ~r1_tarski(sK3,k1_tops_1(sK0,sK2))),
% 1.89/0.62    inference(superposition,[],[f889,f630])).
% 1.89/0.62  fof(f630,plain,(
% 1.89/0.62    sK3 = k2_xboole_0(k2_tarski(sK1,sK1),sK3)),
% 1.89/0.62    inference(resolution,[],[f625,f60])).
% 1.89/0.62  fof(f60,plain,(
% 1.89/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f25])).
% 1.89/0.62  fof(f25,plain,(
% 1.89/0.62    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.89/0.62    inference(ennf_transformation,[],[f3])).
% 1.89/0.62  fof(f3,axiom,(
% 1.89/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.89/0.62  fof(f625,plain,(
% 1.89/0.62    r1_tarski(k2_tarski(sK1,sK1),sK3)),
% 1.89/0.62    inference(subsumption_resolution,[],[f624,f618])).
% 1.89/0.62  % (28692)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.89/0.62  fof(f618,plain,(
% 1.89/0.62    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | r1_tarski(k2_tarski(sK1,sK1),sK3)),
% 1.89/0.62    inference(duplicate_literal_removal,[],[f617])).
% 1.89/0.62  fof(f617,plain,(
% 1.89/0.62    r1_tarski(k2_tarski(sK1,sK1),sK3) | r2_hidden(sK1,k1_tops_1(sK0,sK2)) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 1.89/0.62    inference(resolution,[],[f150,f51])).
% 1.89/0.62  fof(f51,plain,(
% 1.89/0.62    r2_hidden(sK1,sK3) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 1.89/0.62    inference(cnf_transformation,[],[f39])).
% 1.89/0.62  fof(f39,plain,(
% 1.89/0.62    ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) & ((r2_hidden(sK1,sK3) & r1_tarski(sK3,sK2) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.89/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f38,f37,f36])).
% 1.89/0.62  fof(f36,plain,(
% 1.89/0.62    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X2,X1] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X1,k1_tops_1(sK0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(X1,k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.89/0.62    introduced(choice_axiom,[])).
% 1.89/0.62  fof(f37,plain,(
% 1.89/0.62    ? [X2,X1] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X1,k1_tops_1(sK0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(X1,k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) & (? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,sK2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.89/0.62    introduced(choice_axiom,[])).
% 1.89/0.62  fof(f38,plain,(
% 1.89/0.62    ? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,sK2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) => (r2_hidden(sK1,sK3) & r1_tarski(sK3,sK2) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.89/0.62    introduced(choice_axiom,[])).
% 1.89/0.62  fof(f35,plain,(
% 1.89/0.62    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.89/0.62    inference(rectify,[],[f34])).
% 1.89/0.62  fof(f34,plain,(
% 1.89/0.62    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.89/0.62    inference(flattening,[],[f33])).
% 1.89/0.62  fof(f33,plain,(
% 1.89/0.62    ? [X0] : (? [X1,X2] : (((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.89/0.62    inference(nnf_transformation,[],[f17])).
% 1.89/0.62  fof(f17,plain,(
% 1.89/0.62    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.89/0.62    inference(flattening,[],[f16])).
% 1.89/0.62  fof(f16,plain,(
% 1.89/0.62    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.89/0.62    inference(ennf_transformation,[],[f15])).
% 1.89/0.62  % (28696)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.89/0.62  fof(f15,negated_conjecture,(
% 1.89/0.62    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 1.89/0.62    inference(negated_conjecture,[],[f14])).
% 1.89/0.62  fof(f14,conjecture,(
% 1.89/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).
% 1.89/0.62  fof(f150,plain,(
% 1.89/0.62    ( ! [X0] : (~r2_hidden(X0,sK3) | r1_tarski(k2_tarski(sK1,X0),sK3) | r2_hidden(sK1,k1_tops_1(sK0,sK2))) )),
% 1.89/0.62    inference(resolution,[],[f51,f71])).
% 1.89/0.62  fof(f71,plain,(
% 1.89/0.62    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f44])).
% 1.89/0.62  fof(f44,plain,(
% 1.89/0.62    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.89/0.62    inference(flattening,[],[f43])).
% 1.89/0.62  fof(f43,plain,(
% 1.89/0.62    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.89/0.62    inference(nnf_transformation,[],[f4])).
% 1.89/0.62  fof(f4,axiom,(
% 1.89/0.62    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.89/0.62  fof(f624,plain,(
% 1.89/0.62    r1_tarski(k2_tarski(sK1,sK1),sK3) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 1.89/0.62    inference(subsumption_resolution,[],[f623,f110])).
% 1.89/0.62  fof(f110,plain,(
% 1.89/0.62    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.89/0.62    inference(subsumption_resolution,[],[f96,f46])).
% 1.89/0.62  fof(f46,plain,(
% 1.89/0.62    l1_pre_topc(sK0)),
% 1.89/0.62    inference(cnf_transformation,[],[f39])).
% 1.89/0.62  fof(f96,plain,(
% 1.89/0.62    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.89/0.62    inference(resolution,[],[f47,f64])).
% 1.89/0.62  fof(f64,plain,(
% 1.89/0.62    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f31])).
% 1.89/0.62  fof(f31,plain,(
% 1.89/0.62    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.89/0.62    inference(flattening,[],[f30])).
% 1.89/0.62  fof(f30,plain,(
% 1.89/0.62    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.89/0.62    inference(ennf_transformation,[],[f9])).
% 1.89/0.62  fof(f9,axiom,(
% 1.89/0.62    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 1.89/0.62  fof(f47,plain,(
% 1.89/0.62    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.89/0.62    inference(cnf_transformation,[],[f39])).
% 1.89/0.62  fof(f623,plain,(
% 1.89/0.62    r1_tarski(k2_tarski(sK1,sK1),sK3) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 1.89/0.62    inference(subsumption_resolution,[],[f622,f109])).
% 1.89/0.62  fof(f109,plain,(
% 1.89/0.62    v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 1.89/0.62    inference(subsumption_resolution,[],[f108,f45])).
% 1.89/0.62  fof(f45,plain,(
% 1.89/0.62    v2_pre_topc(sK0)),
% 1.89/0.62    inference(cnf_transformation,[],[f39])).
% 1.89/0.62  fof(f108,plain,(
% 1.89/0.62    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~v2_pre_topc(sK0)),
% 1.89/0.62    inference(subsumption_resolution,[],[f95,f46])).
% 1.89/0.62  fof(f95,plain,(
% 1.89/0.62    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.89/0.62    inference(resolution,[],[f47,f63])).
% 1.89/0.62  fof(f63,plain,(
% 1.89/0.62    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f29])).
% 1.89/0.62  fof(f29,plain,(
% 1.89/0.62    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.89/0.62    inference(flattening,[],[f28])).
% 1.89/0.62  fof(f28,plain,(
% 1.89/0.62    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.89/0.62    inference(ennf_transformation,[],[f10])).
% 1.89/0.62  fof(f10,axiom,(
% 1.89/0.62    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 1.89/0.62  fof(f622,plain,(
% 1.89/0.62    r1_tarski(k2_tarski(sK1,sK1),sK3) | ~v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 1.89/0.62    inference(subsumption_resolution,[],[f619,f99])).
% 1.89/0.62  fof(f99,plain,(
% 1.89/0.62    r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 1.89/0.62    inference(subsumption_resolution,[],[f87,f46])).
% 1.89/0.62  fof(f87,plain,(
% 1.89/0.62    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~l1_pre_topc(sK0)),
% 1.89/0.62    inference(resolution,[],[f47,f53])).
% 1.89/0.62  fof(f53,plain,(
% 1.89/0.62    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f18])).
% 1.89/0.62  fof(f18,plain,(
% 1.89/0.62    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.89/0.62    inference(ennf_transformation,[],[f12])).
% 1.89/0.62  fof(f12,axiom,(
% 1.89/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 1.89/0.62  fof(f619,plain,(
% 1.89/0.62    r1_tarski(k2_tarski(sK1,sK1),sK3) | ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 1.89/0.62    inference(resolution,[],[f618,f52])).
% 1.89/0.62  fof(f52,plain,(
% 1.89/0.62    ( ! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) )),
% 1.89/0.62    inference(cnf_transformation,[],[f39])).
% 1.89/0.62  fof(f889,plain,(
% 1.89/0.62    ( ! [X2,X1] : (~r1_tarski(k2_xboole_0(k2_tarski(sK1,X1),X2),k1_tops_1(sK0,sK2))) )),
% 1.89/0.62    inference(resolution,[],[f881,f68])).
% 1.89/0.62  fof(f68,plain,(
% 1.89/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f32])).
% 1.89/0.62  fof(f32,plain,(
% 1.89/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.89/0.62    inference(ennf_transformation,[],[f2])).
% 1.89/0.62  fof(f2,axiom,(
% 1.89/0.62    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.89/0.62  fof(f881,plain,(
% 1.89/0.62    ( ! [X11] : (~r1_tarski(k2_tarski(sK1,X11),k1_tops_1(sK0,sK2))) )),
% 1.89/0.62    inference(subsumption_resolution,[],[f880,f69])).
% 1.89/0.62  fof(f69,plain,(
% 1.89/0.62    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f44])).
% 1.89/0.62  fof(f880,plain,(
% 1.89/0.62    ( ! [X11] : (~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~r1_tarski(k2_tarski(sK1,X11),k1_tops_1(sK0,sK2))) )),
% 1.89/0.62    inference(subsumption_resolution,[],[f879,f110])).
% 1.89/0.62  fof(f879,plain,(
% 1.89/0.62    ( ! [X11] : (~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~r1_tarski(k2_tarski(sK1,X11),k1_tops_1(sK0,sK2))) )),
% 1.89/0.62    inference(subsumption_resolution,[],[f875,f109])).
% 1.89/0.62  fof(f875,plain,(
% 1.89/0.62    ( ! [X11] : (~v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~r1_tarski(k2_tarski(sK1,X11),k1_tops_1(sK0,sK2))) )),
% 1.89/0.62    inference(resolution,[],[f186,f99])).
% 1.89/0.62  fof(f186,plain,(
% 1.89/0.62    ( ! [X0,X1] : (~r1_tarski(X0,sK2) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~r1_tarski(k2_tarski(sK1,X1),X0)) )),
% 1.89/0.62    inference(resolution,[],[f52,f69])).
% 1.89/0.62  fof(f1199,plain,(
% 1.89/0.62    r1_tarski(sK3,k1_tops_1(sK0,sK2))),
% 1.89/0.62    inference(backward_demodulation,[],[f923,f1168])).
% 1.89/0.62  fof(f1168,plain,(
% 1.89/0.62    sK3 = k1_tops_1(sK0,sK3)),
% 1.89/0.62    inference(subsumption_resolution,[],[f1163,f890])).
% 1.89/0.62  fof(f890,plain,(
% 1.89/0.62    ~r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 1.89/0.62    inference(condensation,[],[f888])).
% 1.89/0.62  fof(f888,plain,(
% 1.89/0.62    ( ! [X0] : (~r2_hidden(X0,k1_tops_1(sK0,sK2)) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) )),
% 1.89/0.62    inference(resolution,[],[f881,f71])).
% 1.89/0.62  fof(f1163,plain,(
% 1.89/0.62    sK3 = k1_tops_1(sK0,sK3) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 1.89/0.62    inference(resolution,[],[f1040,f751])).
% 1.89/0.62  fof(f751,plain,(
% 1.89/0.62    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 1.89/0.62    inference(subsumption_resolution,[],[f142,f191])).
% 1.89/0.62  fof(f191,plain,(
% 1.89/0.62    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.89/0.62    inference(subsumption_resolution,[],[f190,f48])).
% 1.89/0.62  fof(f48,plain,(
% 1.89/0.62    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.89/0.62    inference(cnf_transformation,[],[f39])).
% 1.89/0.62  fof(f190,plain,(
% 1.89/0.62    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.89/0.62    inference(subsumption_resolution,[],[f189,f110])).
% 1.89/0.62  fof(f189,plain,(
% 1.89/0.62    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.89/0.62    inference(subsumption_resolution,[],[f188,f109])).
% 1.89/0.62  fof(f188,plain,(
% 1.89/0.62    ~v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.89/0.62    inference(subsumption_resolution,[],[f185,f99])).
% 1.89/0.62  fof(f185,plain,(
% 1.89/0.62    ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.89/0.62    inference(resolution,[],[f52,f48])).
% 1.89/0.62  fof(f142,plain,(
% 1.89/0.62    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.89/0.62    inference(subsumption_resolution,[],[f141,f46])).
% 1.89/0.62  fof(f141,plain,(
% 1.89/0.62    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.89/0.62    inference(resolution,[],[f49,f57])).
% 1.89/0.62  fof(f57,plain,(
% 1.89/0.62    ( ! [X0,X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f40])).
% 1.89/0.62  fof(f40,plain,(
% 1.89/0.62    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.89/0.62    inference(nnf_transformation,[],[f22])).
% 1.89/0.62  fof(f22,plain,(
% 1.89/0.62    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.89/0.62    inference(ennf_transformation,[],[f11])).
% 1.89/0.62  fof(f11,axiom,(
% 1.89/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).
% 1.89/0.62  fof(f49,plain,(
% 1.89/0.62    v3_pre_topc(sK3,sK0) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 1.89/0.62    inference(cnf_transformation,[],[f39])).
% 1.89/0.62  fof(f1040,plain,(
% 1.89/0.62    ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0) | sK3 = k1_tops_1(sK0,sK3)),
% 1.89/0.62    inference(forward_demodulation,[],[f1039,f202])).
% 1.89/0.62  fof(f202,plain,(
% 1.89/0.62    sK3 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3))),
% 1.89/0.62    inference(resolution,[],[f191,f62])).
% 1.89/0.62  fof(f62,plain,(
% 1.89/0.62    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.89/0.62    inference(cnf_transformation,[],[f27])).
% 1.89/0.62  fof(f27,plain,(
% 1.89/0.62    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.89/0.62    inference(ennf_transformation,[],[f6])).
% 1.89/0.62  fof(f6,axiom,(
% 1.89/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.89/0.62  fof(f1039,plain,(
% 1.89/0.62    k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) | ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0)),
% 1.89/0.62    inference(subsumption_resolution,[],[f1031,f203])).
% 1.89/0.62  fof(f203,plain,(
% 1.89/0.62    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.89/0.62    inference(resolution,[],[f191,f61])).
% 1.89/0.62  fof(f61,plain,(
% 1.89/0.62    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.89/0.62    inference(cnf_transformation,[],[f26])).
% 1.89/0.62  fof(f26,plain,(
% 1.89/0.62    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.89/0.62    inference(ennf_transformation,[],[f5])).
% 1.89/0.62  fof(f5,axiom,(
% 1.89/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.89/0.62  fof(f1031,plain,(
% 1.89/0.62    k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) | ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.89/0.62    inference(superposition,[],[f205,f78])).
% 1.89/0.62  fof(f78,plain,(
% 1.89/0.62    ( ! [X2] : (k2_pre_topc(sK0,X2) = X2 | ~v4_pre_topc(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.89/0.62    inference(resolution,[],[f46,f55])).
% 1.89/0.62  fof(f55,plain,(
% 1.89/0.62    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f21])).
% 1.89/0.62  fof(f21,plain,(
% 1.89/0.62    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.89/0.62    inference(flattening,[],[f20])).
% 1.89/0.62  fof(f20,plain,(
% 1.89/0.62    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.89/0.62    inference(ennf_transformation,[],[f7])).
% 1.89/0.62  fof(f7,axiom,(
% 1.89/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.89/0.62  fof(f205,plain,(
% 1.89/0.62    k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)))),
% 1.89/0.62    inference(subsumption_resolution,[],[f193,f46])).
% 1.89/0.62  fof(f193,plain,(
% 1.89/0.62    k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) | ~l1_pre_topc(sK0)),
% 1.89/0.62    inference(resolution,[],[f191,f54])).
% 1.89/0.62  fof(f54,plain,(
% 1.89/0.62    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f19])).
% 1.89/0.62  fof(f19,plain,(
% 1.89/0.62    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.89/0.62    inference(ennf_transformation,[],[f8])).
% 1.89/0.62  fof(f8,axiom,(
% 1.89/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 1.89/0.62  fof(f923,plain,(
% 1.89/0.62    r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))),
% 1.89/0.62    inference(subsumption_resolution,[],[f922,f191])).
% 1.89/0.62  fof(f922,plain,(
% 1.89/0.62    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))),
% 1.89/0.62    inference(subsumption_resolution,[],[f921,f47])).
% 1.89/0.62  fof(f921,plain,(
% 1.89/0.62    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))),
% 1.89/0.62    inference(resolution,[],[f908,f46])).
% 1.89/0.62  fof(f908,plain,(
% 1.89/0.62    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,sK3),k1_tops_1(X0,sK2))) )),
% 1.89/0.62    inference(subsumption_resolution,[],[f149,f890])).
% 1.89/0.62  fof(f149,plain,(
% 1.89/0.62    ( ! [X0] : (r2_hidden(sK1,k1_tops_1(sK0,sK2)) | r1_tarski(k1_tops_1(X0,sK3),k1_tops_1(X0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.62    inference(resolution,[],[f50,f59])).
% 1.89/0.62  fof(f59,plain,(
% 1.89/0.62    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f24])).
% 1.89/0.62  fof(f24,plain,(
% 1.89/0.62    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.89/0.62    inference(flattening,[],[f23])).
% 1.89/0.62  fof(f23,plain,(
% 1.89/0.62    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.89/0.62    inference(ennf_transformation,[],[f13])).
% 1.89/0.62  fof(f13,axiom,(
% 1.89/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 1.89/0.62  fof(f50,plain,(
% 1.89/0.62    r1_tarski(sK3,sK2) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 1.89/0.62    inference(cnf_transformation,[],[f39])).
% 1.89/0.62  % SZS output end Proof for theBenchmark
% 1.89/0.62  % (28687)------------------------------
% 1.89/0.62  % (28687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.62  % (28687)Termination reason: Refutation
% 1.89/0.62  
% 1.89/0.62  % (28687)Memory used [KB]: 2046
% 1.89/0.62  % (28687)Time elapsed: 0.169 s
% 1.89/0.62  % (28687)------------------------------
% 1.89/0.62  % (28687)------------------------------
% 1.89/0.62  % (28678)Success in time 0.261 s
%------------------------------------------------------------------------------
