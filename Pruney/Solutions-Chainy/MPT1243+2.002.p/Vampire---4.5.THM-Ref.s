%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 824 expanded)
%              Number of leaves         :    6 ( 155 expanded)
%              Depth                    :   29
%              Number of atoms          :  228 (4637 expanded)
%              Number of equality atoms :    5 (  40 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f220,plain,(
    $false ),
    inference(subsumption_resolution,[],[f219,f214])).

fof(f214,plain,(
    ~ r2_hidden(sK2,sK1) ),
    inference(subsumption_resolution,[],[f213,f183])).

fof(f183,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f182,f27])).

fof(f27,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( r2_hidden(X2,X1)
              <=> ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r1_tarski(X3,X1)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( r2_hidden(X2,X1)
              <=> ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r1_tarski(X3,X1)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> ! [X2] :
                  ( r2_hidden(X2,X1)
                <=> ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r1_tarski(X3,X1)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,X1)
              <=> ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r1_tarski(X3,X1)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tops_1)).

fof(f182,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f181,f26])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f181,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f180,f28])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f180,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0) ),
    inference(superposition,[],[f31,f142])).

fof(f142,plain,(
    sK1 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f141,f50])).

fof(f50,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f48,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

% (10503)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (10490)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (10508)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (10513)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (10512)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (10507)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (10509)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (10502)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (10497)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (10504)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (10510)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (10514)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (10493)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (10501)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f48,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f47,f26])).

fof(f47,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,X0),X0) ) ),
    inference(resolution,[],[f29,f28])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f141,plain,(
    r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f140,f118])).

fof(f118,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f116,f38])).

fof(f38,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f116,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ r1_tarski(sK1,sK1)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f114,f26])).

fof(f114,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | ~ r1_tarski(X0,sK1)
      | r1_tarski(X0,k1_tops_1(sK0,sK1)) ) ),
    inference(resolution,[],[f113,f26])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k1_tops_1(sK0,X1)) ) ),
    inference(resolution,[],[f30,f28])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f140,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f136,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f136,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK1,X0),k1_tops_1(sK0,sK1))
      | r1_tarski(sK1,X0)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,(
    ! [X0] :
      ( v3_pre_topc(sK1,sK0)
      | r1_tarski(sK1,X0)
      | r2_hidden(sK5(sK1,X0),k1_tops_1(sK0,sK1))
      | v3_pre_topc(sK1,sK0)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f121,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK4(sK5(sK1,X0)),X1)
      | r2_hidden(sK5(sK1,X0),X1)
      | v3_pre_topc(sK1,sK0)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f44,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r1_tarski(sK4(X0),X1)
      | r2_hidden(X0,X1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(resolution,[],[f35,f19])).

fof(f19,plain,(
    ! [X2] :
      ( r2_hidden(X2,sK4(X2))
      | ~ r2_hidden(X2,sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f121,plain,(
    ! [X0] :
      ( r1_tarski(sK4(sK5(sK1,X0)),k1_tops_1(sK0,sK1))
      | v3_pre_topc(sK1,sK0)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f120,f36])).

fof(f120,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r1_tarski(sK4(X0),k1_tops_1(sK0,sK1))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f119,f18])).

fof(f18,plain,(
    ! [X2] :
      ( r1_tarski(sK4(X2),sK1)
      | ~ r2_hidden(X2,sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f119,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK4(X0),sK1)
      | r1_tarski(sK4(X0),k1_tops_1(sK0,sK1))
      | ~ r2_hidden(X0,sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f117,f17])).

fof(f17,plain,(
    ! [X2] :
      ( v3_pre_topc(sK4(X2),sK0)
      | ~ r2_hidden(X2,sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f117,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(sK4(X0),sK0)
      | ~ r1_tarski(sK4(X0),sK1)
      | r1_tarski(sK4(X0),k1_tops_1(sK0,sK1))
      | ~ r2_hidden(X0,sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(resolution,[],[f114,f16])).

fof(f16,plain,(
    ! [X2] :
      ( m1_subset_1(sK4(X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f213,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f210,f38])).

fof(f210,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ r2_hidden(sK2,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f188,f26])).

fof(f188,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | ~ r2_hidden(sK2,X0)
      | ~ v3_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f184,f35])).

fof(f184,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ r1_tarski(X0,sK1)
      | ~ r2_hidden(sK2,X0)
      | ~ r2_hidden(sK2,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f183,f21])).

fof(f21,plain,(
    ! [X3] :
      ( ~ v3_pre_topc(sK1,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK1)
      | ~ r2_hidden(sK2,X3)
      | ~ r2_hidden(sK2,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f219,plain,(
    r2_hidden(sK2,sK1) ),
    inference(duplicate_literal_removal,[],[f216])).

fof(f216,plain,
    ( r2_hidden(sK2,sK1)
    | r2_hidden(sK2,sK1) ),
    inference(resolution,[],[f215,f189])).

fof(f189,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK3,X0)
      | r2_hidden(sK2,X0)
      | r2_hidden(sK2,sK1) ) ),
    inference(resolution,[],[f186,f35])).

fof(f186,plain,
    ( r2_hidden(sK2,sK3)
    | r2_hidden(sK2,sK1) ),
    inference(resolution,[],[f183,f25])).

fof(f25,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r2_hidden(sK2,sK1)
    | r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f215,plain,(
    r1_tarski(sK3,sK1) ),
    inference(resolution,[],[f214,f187])).

fof(f187,plain,
    ( r2_hidden(sK2,sK1)
    | r1_tarski(sK3,sK1) ),
    inference(resolution,[],[f183,f24])).

fof(f24,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r2_hidden(sK2,sK1)
    | r1_tarski(sK3,sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:58:38 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.50  % (10491)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (10500)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.50  % (10499)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (10485)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (10498)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (10492)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (10495)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (10486)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (10505)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (10487)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (10489)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (10495)Refutation not found, incomplete strategy% (10495)------------------------------
% 0.20/0.52  % (10495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10495)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (10495)Memory used [KB]: 10746
% 0.20/0.52  % (10495)Time elapsed: 0.128 s
% 0.20/0.52  % (10495)------------------------------
% 0.20/0.52  % (10495)------------------------------
% 0.20/0.52  % (10491)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f220,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f219,f214])).
% 0.20/0.52  fof(f214,plain,(
% 0.20/0.52    ~r2_hidden(sK2,sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f213,f183])).
% 0.20/0.52  fof(f183,plain,(
% 0.20/0.52    v3_pre_topc(sK1,sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f182,f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    v2_pre_topc(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f8])).
% 0.20/0.52  fof(f8,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,negated_conjecture,(
% 0.20/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.20/0.52    inference(negated_conjecture,[],[f6])).
% 0.20/0.52  fof(f6,conjecture,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tops_1)).
% 0.20/0.52  fof(f182,plain,(
% 0.20/0.52    v3_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f181,f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f181,plain,(
% 0.20/0.52    v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f180,f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    l1_pre_topc(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f180,plain,(
% 0.20/0.52    v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)),
% 0.20/0.52    inference(superposition,[],[f31,f142])).
% 0.20/0.52  fof(f142,plain,(
% 0.20/0.52    sK1 = k1_tops_1(sK0,sK1)),
% 0.20/0.52    inference(resolution,[],[f141,f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | sK1 = k1_tops_1(sK0,sK1)),
% 0.20/0.52    inference(resolution,[],[f48,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.52  % (10503)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (10490)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (10508)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.36/0.53  % (10513)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.53  % (10512)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.53  % (10507)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.36/0.53  % (10509)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.53  % (10502)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.36/0.53  % (10497)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.53  % (10504)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.36/0.54  % (10510)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.36/0.54  % (10514)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.54  % (10493)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.36/0.54  % (10501)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.36/0.54  fof(f48,plain,(
% 1.36/0.54    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.36/0.54    inference(resolution,[],[f47,f26])).
% 1.36/0.54  fof(f47,plain,(
% 1.36/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0)) )),
% 1.36/0.54    inference(resolution,[],[f29,f28])).
% 1.36/0.54  fof(f29,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f10])).
% 1.36/0.54  fof(f10,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.36/0.54    inference(ennf_transformation,[],[f4])).
% 1.36/0.54  fof(f4,axiom,(
% 1.36/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 1.36/0.54  fof(f141,plain,(
% 1.36/0.54    r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 1.36/0.54    inference(subsumption_resolution,[],[f140,f118])).
% 1.36/0.54  fof(f118,plain,(
% 1.36/0.54    ~v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 1.36/0.54    inference(subsumption_resolution,[],[f116,f38])).
% 1.36/0.54  fof(f38,plain,(
% 1.36/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.36/0.54    inference(equality_resolution,[],[f33])).
% 1.36/0.54  fof(f33,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.36/0.54    inference(cnf_transformation,[],[f2])).
% 1.36/0.54  fof(f116,plain,(
% 1.36/0.54    ~v3_pre_topc(sK1,sK0) | ~r1_tarski(sK1,sK1) | r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 1.36/0.54    inference(resolution,[],[f114,f26])).
% 1.36/0.54  fof(f114,plain,(
% 1.36/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,sK1) | r1_tarski(X0,k1_tops_1(sK0,sK1))) )),
% 1.36/0.54    inference(resolution,[],[f113,f26])).
% 1.36/0.54  fof(f113,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,X1) | r1_tarski(X0,k1_tops_1(sK0,X1))) )),
% 1.36/0.54    inference(resolution,[],[f30,f28])).
% 1.36/0.54  fof(f30,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~r1_tarski(X1,X2) | r1_tarski(X1,k1_tops_1(X0,X2))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f12])).
% 1.36/0.54  fof(f12,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.36/0.54    inference(flattening,[],[f11])).
% 1.36/0.54  fof(f11,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.36/0.54    inference(ennf_transformation,[],[f5])).
% 1.36/0.54  fof(f5,axiom,(
% 1.36/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 1.36/0.54  fof(f140,plain,(
% 1.36/0.54    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0)),
% 1.36/0.54    inference(duplicate_literal_removal,[],[f138])).
% 1.36/0.54  fof(f138,plain,(
% 1.36/0.54    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 1.36/0.54    inference(resolution,[],[f136,f37])).
% 1.36/0.54  fof(f37,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f15])).
% 1.36/0.54  fof(f15,plain,(
% 1.36/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.36/0.54    inference(ennf_transformation,[],[f1])).
% 1.36/0.54  fof(f1,axiom,(
% 1.36/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.36/0.54  fof(f136,plain,(
% 1.36/0.54    ( ! [X0] : (r2_hidden(sK5(sK1,X0),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,X0) | v3_pre_topc(sK1,sK0)) )),
% 1.36/0.54    inference(duplicate_literal_removal,[],[f128])).
% 1.36/0.54  fof(f128,plain,(
% 1.36/0.54    ( ! [X0] : (v3_pre_topc(sK1,sK0) | r1_tarski(sK1,X0) | r2_hidden(sK5(sK1,X0),k1_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0) | r1_tarski(sK1,X0)) )),
% 1.36/0.54    inference(resolution,[],[f121,f46])).
% 1.36/0.54  fof(f46,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~r1_tarski(sK4(sK5(sK1,X0)),X1) | r2_hidden(sK5(sK1,X0),X1) | v3_pre_topc(sK1,sK0) | r1_tarski(sK1,X0)) )),
% 1.36/0.54    inference(resolution,[],[f44,f36])).
% 1.36/0.54  fof(f36,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f15])).
% 1.36/0.54  fof(f44,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~r1_tarski(sK4(X0),X1) | r2_hidden(X0,X1) | v3_pre_topc(sK1,sK0)) )),
% 1.36/0.54    inference(resolution,[],[f35,f19])).
% 1.36/0.54  fof(f19,plain,(
% 1.36/0.54    ( ! [X2] : (r2_hidden(X2,sK4(X2)) | ~r2_hidden(X2,sK1) | v3_pre_topc(sK1,sK0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f9])).
% 1.36/0.54  fof(f35,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f15])).
% 1.36/0.54  fof(f121,plain,(
% 1.36/0.54    ( ! [X0] : (r1_tarski(sK4(sK5(sK1,X0)),k1_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0) | r1_tarski(sK1,X0)) )),
% 1.36/0.54    inference(resolution,[],[f120,f36])).
% 1.36/0.54  fof(f120,plain,(
% 1.36/0.54    ( ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(sK4(X0),k1_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0)) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f119,f18])).
% 1.36/0.54  fof(f18,plain,(
% 1.36/0.54    ( ! [X2] : (r1_tarski(sK4(X2),sK1) | ~r2_hidden(X2,sK1) | v3_pre_topc(sK1,sK0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f9])).
% 1.36/0.54  fof(f119,plain,(
% 1.36/0.54    ( ! [X0] : (~r1_tarski(sK4(X0),sK1) | r1_tarski(sK4(X0),k1_tops_1(sK0,sK1)) | ~r2_hidden(X0,sK1) | v3_pre_topc(sK1,sK0)) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f117,f17])).
% 1.36/0.54  fof(f17,plain,(
% 1.36/0.54    ( ! [X2] : (v3_pre_topc(sK4(X2),sK0) | ~r2_hidden(X2,sK1) | v3_pre_topc(sK1,sK0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f9])).
% 1.36/0.54  fof(f117,plain,(
% 1.36/0.54    ( ! [X0] : (~v3_pre_topc(sK4(X0),sK0) | ~r1_tarski(sK4(X0),sK1) | r1_tarski(sK4(X0),k1_tops_1(sK0,sK1)) | ~r2_hidden(X0,sK1) | v3_pre_topc(sK1,sK0)) )),
% 1.36/0.54    inference(resolution,[],[f114,f16])).
% 1.36/0.54  fof(f16,plain,(
% 1.36/0.54    ( ! [X2] : (m1_subset_1(sK4(X2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,sK1) | v3_pre_topc(sK1,sK0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f9])).
% 1.36/0.54  fof(f31,plain,(
% 1.36/0.54    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f14])).
% 1.36/0.54  fof(f14,plain,(
% 1.36/0.54    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.36/0.54    inference(flattening,[],[f13])).
% 1.36/0.54  fof(f13,plain,(
% 1.36/0.54    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.36/0.54    inference(ennf_transformation,[],[f3])).
% 1.36/0.54  fof(f3,axiom,(
% 1.36/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 1.36/0.54  fof(f213,plain,(
% 1.36/0.54    ~r2_hidden(sK2,sK1) | ~v3_pre_topc(sK1,sK0)),
% 1.36/0.54    inference(subsumption_resolution,[],[f210,f38])).
% 1.36/0.54  fof(f210,plain,(
% 1.36/0.54    ~r1_tarski(sK1,sK1) | ~r2_hidden(sK2,sK1) | ~v3_pre_topc(sK1,sK0)),
% 1.36/0.54    inference(resolution,[],[f188,f26])).
% 1.36/0.54  fof(f188,plain,(
% 1.36/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | ~r2_hidden(sK2,X0) | ~v3_pre_topc(X0,sK0)) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f184,f35])).
% 1.36/0.54  fof(f184,plain,(
% 1.36/0.54    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,sK1) | ~r2_hidden(sK2,X0) | ~r2_hidden(sK2,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.36/0.54    inference(resolution,[],[f183,f21])).
% 1.36/0.54  fof(f21,plain,(
% 1.36/0.54    ( ! [X3] : (~v3_pre_topc(sK1,sK0) | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~r2_hidden(sK2,X3) | ~r2_hidden(sK2,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f9])).
% 1.36/0.54  fof(f219,plain,(
% 1.36/0.54    r2_hidden(sK2,sK1)),
% 1.36/0.54    inference(duplicate_literal_removal,[],[f216])).
% 1.36/0.54  fof(f216,plain,(
% 1.36/0.54    r2_hidden(sK2,sK1) | r2_hidden(sK2,sK1)),
% 1.36/0.54    inference(resolution,[],[f215,f189])).
% 1.36/0.54  fof(f189,plain,(
% 1.36/0.54    ( ! [X0] : (~r1_tarski(sK3,X0) | r2_hidden(sK2,X0) | r2_hidden(sK2,sK1)) )),
% 1.36/0.54    inference(resolution,[],[f186,f35])).
% 1.36/0.54  fof(f186,plain,(
% 1.36/0.54    r2_hidden(sK2,sK3) | r2_hidden(sK2,sK1)),
% 1.36/0.54    inference(resolution,[],[f183,f25])).
% 1.36/0.54  fof(f25,plain,(
% 1.36/0.54    ~v3_pre_topc(sK1,sK0) | r2_hidden(sK2,sK1) | r2_hidden(sK2,sK3)),
% 1.36/0.54    inference(cnf_transformation,[],[f9])).
% 1.36/0.54  fof(f215,plain,(
% 1.36/0.54    r1_tarski(sK3,sK1)),
% 1.36/0.54    inference(resolution,[],[f214,f187])).
% 1.36/0.54  fof(f187,plain,(
% 1.36/0.54    r2_hidden(sK2,sK1) | r1_tarski(sK3,sK1)),
% 1.36/0.54    inference(resolution,[],[f183,f24])).
% 1.36/0.54  fof(f24,plain,(
% 1.36/0.54    ~v3_pre_topc(sK1,sK0) | r2_hidden(sK2,sK1) | r1_tarski(sK3,sK1)),
% 1.36/0.54    inference(cnf_transformation,[],[f9])).
% 1.36/0.54  % SZS output end Proof for theBenchmark
% 1.36/0.54  % (10491)------------------------------
% 1.36/0.54  % (10491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (10491)Termination reason: Refutation
% 1.36/0.54  
% 1.36/0.54  % (10491)Memory used [KB]: 6268
% 1.36/0.54  % (10491)Time elapsed: 0.122 s
% 1.36/0.54  % (10491)------------------------------
% 1.36/0.54  % (10491)------------------------------
% 1.51/0.54  % (10484)Success in time 0.194 s
%------------------------------------------------------------------------------
