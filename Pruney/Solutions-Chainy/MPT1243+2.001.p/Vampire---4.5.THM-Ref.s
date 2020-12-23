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
% DateTime   : Thu Dec  3 13:11:20 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   70 (1387 expanded)
%              Number of leaves         :    6 ( 263 expanded)
%              Depth                    :   30
%              Number of atoms          :  257 (8152 expanded)
%              Number of equality atoms :   20 ( 246 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(subsumption_resolution,[],[f134,f115])).

% (11431)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (11433)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (11443)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (11432)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (11428)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (11423)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (11415)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% (11425)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (11424)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (11434)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (11439)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f115,plain,(
    ~ r2_hidden(sK2,sK1) ),
    inference(subsumption_resolution,[],[f114,f100])).

fof(f100,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f97,f26])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
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

fof(f97,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f51,f92])).

fof(f92,plain,(
    sK1 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f91,f26])).

fof(f91,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f86,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_tops_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = X0 ) ),
    inference(resolution,[],[f50,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f50,plain,(
    ! [X10] :
      ( r1_tarski(k1_tops_1(sK0,X10),X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f28,f29])).

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

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f86,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f85,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
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

fof(f85,plain,
    ( ~ r2_hidden(sK6(sK1,k1_tops_1(sK0,sK1)),sK1)
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f84,f79])).

fof(f79,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ r2_hidden(sK6(sK1,k1_tops_1(sK0,sK1)),sK1)
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f74,f43])).

fof(f43,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f74,plain,
    ( ~ r2_hidden(sK6(sK1,k1_tops_1(sK0,sK1)),sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ r1_tarski(sK1,sK1)
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f64,f26])).

fof(f64,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK6(sK1,k1_tops_1(sK0,sK1)),X3)
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK1)
      | sK1 = k1_tops_1(sK0,sK1) ) ),
    inference(resolution,[],[f62,f26])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,X1)
      | ~ r2_hidden(sK6(X1,k1_tops_1(sK0,X1)),X0)
      | ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,X1) = X1 ) ),
    inference(duplicate_literal_removal,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ r1_tarski(X0,X1)
      | ~ r2_hidden(sK6(X1,k1_tops_1(sK0,X1)),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,X1) = X1 ) ),
    inference(resolution,[],[f59,f57])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k1_tops_1(sK0,X1))
      | ~ v3_pre_topc(X0,sK0)
      | ~ r1_tarski(X0,X1)
      | ~ r2_hidden(sK6(X2,k1_tops_1(sK0,X1)),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f55,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,(
    ! [X8,X7,X9] :
      ( r2_hidden(X9,k1_tops_1(sK0,X7))
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X8,sK0)
      | ~ r1_tarski(X8,X7)
      | ~ r2_hidden(X9,X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f49,f27])).

fof(f27,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X8,X7,X9] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X8,sK0)
      | ~ r1_tarski(X8,X7)
      | ~ r2_hidden(X9,X8)
      | r2_hidden(X9,k1_tops_1(sK0,X7)) ) ),
    inference(resolution,[],[f28,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | ~ r1_tarski(X3,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

fof(f84,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r2_hidden(sK6(sK1,k1_tops_1(sK0,sK1)),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r2_hidden(sK6(sK1,k1_tops_1(sK0,sK1)),sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ r2_hidden(sK6(sK1,k1_tops_1(sK0,sK1)),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f81,f19])).

fof(f19,plain,(
    ! [X2] :
      ( r2_hidden(X2,sK4(X2))
      | ~ r2_hidden(X2,sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f81,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK6(sK1,k1_tops_1(sK0,sK1)),sK4(X2))
      | sK1 = k1_tops_1(sK0,sK1)
      | ~ r2_hidden(X2,sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f80,f18])).

fof(f18,plain,(
    ! [X2] :
      ( r1_tarski(sK4(X2),sK1)
      | ~ r2_hidden(X2,sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f80,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK6(sK1,k1_tops_1(sK0,sK1)),sK4(X2))
      | ~ r1_tarski(sK4(X2),sK1)
      | sK1 = k1_tops_1(sK0,sK1)
      | ~ r2_hidden(X2,sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f75,f17])).

fof(f17,plain,(
    ! [X2] :
      ( v3_pre_topc(sK4(X2),sK0)
      | ~ r2_hidden(X2,sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f75,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK6(sK1,k1_tops_1(sK0,sK1)),sK4(X2))
      | ~ v3_pre_topc(sK4(X2),sK0)
      | ~ r1_tarski(sK4(X2),sK1)
      | sK1 = k1_tops_1(sK0,sK1)
      | ~ r2_hidden(X2,sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(resolution,[],[f64,f16])).

fof(f16,plain,(
    ! [X2] :
      ( m1_subset_1(sK4(X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X0] :
      ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f45,f27])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(k1_tops_1(sK0,X0),sK0) ) ),
    inference(resolution,[],[f28,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
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

fof(f114,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f109,f43])).

fof(f109,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ r2_hidden(sK2,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f101,f26])).

fof(f101,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | ~ r2_hidden(sK2,X0)
      | ~ v3_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f100,f44])).

fof(f44,plain,(
    ! [X3] :
      ( ~ v3_pre_topc(sK1,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK1)
      | ~ r2_hidden(sK2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f21,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f21,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK1)
      | ~ r2_hidden(sK2,X3)
      | ~ r2_hidden(sK2,sK1)
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f134,plain,(
    r2_hidden(sK2,sK1) ),
    inference(resolution,[],[f127,f103])).

fof(f103,plain,
    ( r2_hidden(sK2,sK3)
    | r2_hidden(sK2,sK1) ),
    inference(resolution,[],[f100,f25])).

fof(f25,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r2_hidden(sK2,sK1)
    | r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f127,plain,(
    ~ r2_hidden(sK2,sK3) ),
    inference(resolution,[],[f118,f117])).

fof(f117,plain,(
    r1_tarski(sK3,sK1) ),
    inference(resolution,[],[f115,f104])).

fof(f104,plain,
    ( r2_hidden(sK2,sK1)
    | r1_tarski(sK3,sK1) ),
    inference(resolution,[],[f100,f24])).

fof(f24,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r2_hidden(sK2,sK1)
    | r1_tarski(sK3,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f118,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ r2_hidden(sK2,X0) ) ),
    inference(resolution,[],[f115,f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:38:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (11438)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (11429)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (11421)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (11418)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (11416)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (11445)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (11426)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (11435)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (11420)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (11427)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (11444)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.46/0.56  % (11417)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.46/0.57  % (11419)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.46/0.57  % (11442)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.46/0.57  % (11437)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.46/0.57  % (11441)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.46/0.57  % (11440)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.46/0.57  % (11442)Refutation not found, incomplete strategy% (11442)------------------------------
% 1.46/0.57  % (11442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.57  % (11442)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.57  
% 1.46/0.57  % (11442)Memory used [KB]: 10746
% 1.46/0.57  % (11442)Time elapsed: 0.162 s
% 1.46/0.57  % (11442)------------------------------
% 1.46/0.57  % (11442)------------------------------
% 1.46/0.58  % (11437)Refutation found. Thanks to Tanya!
% 1.46/0.58  % SZS status Theorem for theBenchmark
% 1.46/0.58  % SZS output start Proof for theBenchmark
% 1.46/0.58  fof(f136,plain,(
% 1.46/0.58    $false),
% 1.46/0.58    inference(subsumption_resolution,[],[f134,f115])).
% 1.46/0.58  % (11431)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.70/0.58  % (11433)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.70/0.58  % (11443)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.70/0.58  % (11432)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.70/0.59  % (11428)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.70/0.59  % (11423)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.70/0.59  % (11415)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.70/0.59  % (11425)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.70/0.59  % (11424)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.70/0.59  % (11434)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.70/0.60  % (11439)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.70/0.61  fof(f115,plain,(
% 1.70/0.61    ~r2_hidden(sK2,sK1)),
% 1.70/0.61    inference(subsumption_resolution,[],[f114,f100])).
% 1.70/0.61  fof(f100,plain,(
% 1.70/0.61    v3_pre_topc(sK1,sK0)),
% 1.70/0.61    inference(subsumption_resolution,[],[f97,f26])).
% 1.70/0.61  fof(f26,plain,(
% 1.70/0.61    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.70/0.61    inference(cnf_transformation,[],[f9])).
% 1.70/0.61  fof(f9,plain,(
% 1.70/0.61    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.70/0.61    inference(flattening,[],[f8])).
% 1.70/0.61  fof(f8,plain,(
% 1.70/0.61    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.70/0.61    inference(ennf_transformation,[],[f7])).
% 1.70/0.61  fof(f7,negated_conjecture,(
% 1.70/0.61    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 1.70/0.61    inference(negated_conjecture,[],[f6])).
% 1.70/0.61  fof(f6,conjecture,(
% 1.70/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tops_1)).
% 1.70/0.61  fof(f97,plain,(
% 1.70/0.61    v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.70/0.61    inference(superposition,[],[f51,f92])).
% 1.70/0.61  fof(f92,plain,(
% 1.70/0.61    sK1 = k1_tops_1(sK0,sK1)),
% 1.70/0.61    inference(subsumption_resolution,[],[f91,f26])).
% 1.70/0.61  fof(f91,plain,(
% 1.70/0.61    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.70/0.61    inference(duplicate_literal_removal,[],[f88])).
% 1.70/0.61  fof(f88,plain,(
% 1.70/0.61    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k1_tops_1(sK0,sK1)),
% 1.70/0.61    inference(resolution,[],[f86,f57])).
% 1.70/0.61  fof(f57,plain,(
% 1.70/0.61    ( ! [X0] : (~r1_tarski(X0,k1_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = X0) )),
% 1.70/0.61    inference(resolution,[],[f50,f38])).
% 1.70/0.61  fof(f38,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.70/0.61    inference(cnf_transformation,[],[f2])).
% 1.70/0.61  fof(f2,axiom,(
% 1.70/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.70/0.61  fof(f50,plain,(
% 1.70/0.61    ( ! [X10] : (r1_tarski(k1_tops_1(sK0,X10),X10) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.70/0.61    inference(resolution,[],[f28,f29])).
% 1.70/0.61  fof(f29,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f10])).
% 1.70/0.61  fof(f10,plain,(
% 1.70/0.61    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.70/0.61    inference(ennf_transformation,[],[f4])).
% 1.70/0.61  fof(f4,axiom,(
% 1.70/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 1.70/0.61  fof(f28,plain,(
% 1.70/0.61    l1_pre_topc(sK0)),
% 1.70/0.61    inference(cnf_transformation,[],[f9])).
% 1.70/0.61  fof(f86,plain,(
% 1.70/0.61    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | sK1 = k1_tops_1(sK0,sK1)),
% 1.70/0.61    inference(resolution,[],[f85,f40])).
% 1.70/0.61  fof(f40,plain,(
% 1.70/0.61    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f15])).
% 1.70/0.61  fof(f15,plain,(
% 1.70/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.70/0.61    inference(ennf_transformation,[],[f1])).
% 1.70/0.61  fof(f1,axiom,(
% 1.70/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.70/0.61  fof(f85,plain,(
% 1.70/0.61    ~r2_hidden(sK6(sK1,k1_tops_1(sK0,sK1)),sK1) | sK1 = k1_tops_1(sK0,sK1)),
% 1.70/0.61    inference(subsumption_resolution,[],[f84,f79])).
% 1.70/0.61  fof(f79,plain,(
% 1.70/0.61    ~v3_pre_topc(sK1,sK0) | ~r2_hidden(sK6(sK1,k1_tops_1(sK0,sK1)),sK1) | sK1 = k1_tops_1(sK0,sK1)),
% 1.70/0.61    inference(subsumption_resolution,[],[f74,f43])).
% 1.70/0.61  fof(f43,plain,(
% 1.70/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.70/0.61    inference(equality_resolution,[],[f36])).
% 1.70/0.61  fof(f36,plain,(
% 1.70/0.61    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.70/0.61    inference(cnf_transformation,[],[f2])).
% 1.70/0.61  fof(f74,plain,(
% 1.70/0.61    ~r2_hidden(sK6(sK1,k1_tops_1(sK0,sK1)),sK1) | ~v3_pre_topc(sK1,sK0) | ~r1_tarski(sK1,sK1) | sK1 = k1_tops_1(sK0,sK1)),
% 1.70/0.61    inference(resolution,[],[f64,f26])).
% 1.70/0.61  fof(f64,plain,(
% 1.70/0.61    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK6(sK1,k1_tops_1(sK0,sK1)),X3) | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | sK1 = k1_tops_1(sK0,sK1)) )),
% 1.70/0.61    inference(resolution,[],[f62,f26])).
% 1.70/0.61  fof(f62,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,X1) | ~r2_hidden(sK6(X1,k1_tops_1(sK0,X1)),X0) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X1) = X1) )),
% 1.70/0.61    inference(duplicate_literal_removal,[],[f60])).
% 1.70/0.61  fof(f60,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,X1) | ~r2_hidden(sK6(X1,k1_tops_1(sK0,X1)),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X1) = X1) )),
% 1.70/0.61    inference(resolution,[],[f59,f57])).
% 1.70/0.61  fof(f59,plain,(
% 1.70/0.61    ( ! [X2,X0,X1] : (r1_tarski(X2,k1_tops_1(sK0,X1)) | ~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,X1) | ~r2_hidden(sK6(X2,k1_tops_1(sK0,X1)),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.70/0.61    inference(resolution,[],[f55,f41])).
% 1.70/0.61  fof(f41,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f15])).
% 1.70/0.61  fof(f55,plain,(
% 1.70/0.61    ( ! [X8,X7,X9] : (r2_hidden(X9,k1_tops_1(sK0,X7)) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X8,sK0) | ~r1_tarski(X8,X7) | ~r2_hidden(X9,X8) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f49,f27])).
% 1.70/0.61  fof(f27,plain,(
% 1.70/0.61    v2_pre_topc(sK0)),
% 1.70/0.61    inference(cnf_transformation,[],[f9])).
% 1.70/0.61  fof(f49,plain,(
% 1.70/0.61    ( ! [X8,X7,X9] : (~v2_pre_topc(sK0) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X8,sK0) | ~r1_tarski(X8,X7) | ~r2_hidden(X9,X8) | r2_hidden(X9,k1_tops_1(sK0,X7))) )),
% 1.70/0.61    inference(resolution,[],[f28,f34])).
% 1.70/0.61  fof(f34,plain,(
% 1.70/0.61    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X2) | ~r2_hidden(X1,X3) | r2_hidden(X1,k1_tops_1(X0,X2))) )),
% 1.70/0.61    inference(cnf_transformation,[],[f12])).
% 1.70/0.61  fof(f12,plain,(
% 1.70/0.61    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.70/0.61    inference(flattening,[],[f11])).
% 1.70/0.61  fof(f11,plain,(
% 1.70/0.61    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.70/0.61    inference(ennf_transformation,[],[f5])).
% 1.70/0.61  fof(f5,axiom,(
% 1.70/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).
% 1.70/0.61  fof(f84,plain,(
% 1.70/0.61    sK1 = k1_tops_1(sK0,sK1) | ~r2_hidden(sK6(sK1,k1_tops_1(sK0,sK1)),sK1) | v3_pre_topc(sK1,sK0)),
% 1.70/0.61    inference(duplicate_literal_removal,[],[f82])).
% 1.70/0.61  fof(f82,plain,(
% 1.70/0.61    sK1 = k1_tops_1(sK0,sK1) | ~r2_hidden(sK6(sK1,k1_tops_1(sK0,sK1)),sK1) | v3_pre_topc(sK1,sK0) | ~r2_hidden(sK6(sK1,k1_tops_1(sK0,sK1)),sK1) | v3_pre_topc(sK1,sK0)),
% 1.70/0.61    inference(resolution,[],[f81,f19])).
% 1.70/0.61  fof(f19,plain,(
% 1.70/0.61    ( ! [X2] : (r2_hidden(X2,sK4(X2)) | ~r2_hidden(X2,sK1) | v3_pre_topc(sK1,sK0)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f9])).
% 1.70/0.61  fof(f81,plain,(
% 1.70/0.61    ( ! [X2] : (~r2_hidden(sK6(sK1,k1_tops_1(sK0,sK1)),sK4(X2)) | sK1 = k1_tops_1(sK0,sK1) | ~r2_hidden(X2,sK1) | v3_pre_topc(sK1,sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f80,f18])).
% 1.70/0.61  fof(f18,plain,(
% 1.70/0.61    ( ! [X2] : (r1_tarski(sK4(X2),sK1) | ~r2_hidden(X2,sK1) | v3_pre_topc(sK1,sK0)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f9])).
% 1.70/0.61  fof(f80,plain,(
% 1.70/0.61    ( ! [X2] : (~r2_hidden(sK6(sK1,k1_tops_1(sK0,sK1)),sK4(X2)) | ~r1_tarski(sK4(X2),sK1) | sK1 = k1_tops_1(sK0,sK1) | ~r2_hidden(X2,sK1) | v3_pre_topc(sK1,sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f75,f17])).
% 1.70/0.61  fof(f17,plain,(
% 1.70/0.61    ( ! [X2] : (v3_pre_topc(sK4(X2),sK0) | ~r2_hidden(X2,sK1) | v3_pre_topc(sK1,sK0)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f9])).
% 1.70/0.61  fof(f75,plain,(
% 1.70/0.61    ( ! [X2] : (~r2_hidden(sK6(sK1,k1_tops_1(sK0,sK1)),sK4(X2)) | ~v3_pre_topc(sK4(X2),sK0) | ~r1_tarski(sK4(X2),sK1) | sK1 = k1_tops_1(sK0,sK1) | ~r2_hidden(X2,sK1) | v3_pre_topc(sK1,sK0)) )),
% 1.70/0.61    inference(resolution,[],[f64,f16])).
% 1.70/0.61  fof(f16,plain,(
% 1.70/0.61    ( ! [X2] : (m1_subset_1(sK4(X2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,sK1) | v3_pre_topc(sK1,sK0)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f9])).
% 1.70/0.61  fof(f51,plain,(
% 1.70/0.61    ( ! [X0] : (v3_pre_topc(k1_tops_1(sK0,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f45,f27])).
% 1.70/0.61  fof(f45,plain,(
% 1.70/0.61    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k1_tops_1(sK0,X0),sK0)) )),
% 1.70/0.61    inference(resolution,[],[f28,f35])).
% 1.70/0.61  fof(f35,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f14])).
% 1.70/0.61  fof(f14,plain,(
% 1.70/0.61    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.70/0.61    inference(flattening,[],[f13])).
% 1.70/0.61  fof(f13,plain,(
% 1.70/0.61    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.70/0.61    inference(ennf_transformation,[],[f3])).
% 1.70/0.61  fof(f3,axiom,(
% 1.70/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.70/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 1.70/0.61  fof(f114,plain,(
% 1.70/0.61    ~r2_hidden(sK2,sK1) | ~v3_pre_topc(sK1,sK0)),
% 1.70/0.61    inference(subsumption_resolution,[],[f109,f43])).
% 1.70/0.61  fof(f109,plain,(
% 1.70/0.61    ~r1_tarski(sK1,sK1) | ~r2_hidden(sK2,sK1) | ~v3_pre_topc(sK1,sK0)),
% 1.70/0.61    inference(resolution,[],[f101,f26])).
% 1.70/0.61  fof(f101,plain,(
% 1.70/0.61    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | ~r2_hidden(sK2,X0) | ~v3_pre_topc(X0,sK0)) )),
% 1.70/0.61    inference(resolution,[],[f100,f44])).
% 1.70/0.61  fof(f44,plain,(
% 1.70/0.61    ( ! [X3] : (~v3_pre_topc(sK1,sK0) | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~r2_hidden(sK2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f21,f39])).
% 1.70/0.61  fof(f39,plain,(
% 1.70/0.61    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f15])).
% 1.70/0.61  fof(f21,plain,(
% 1.70/0.61    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~r2_hidden(sK2,X3) | ~r2_hidden(sK2,sK1) | ~v3_pre_topc(sK1,sK0)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f9])).
% 1.70/0.61  fof(f134,plain,(
% 1.70/0.61    r2_hidden(sK2,sK1)),
% 1.70/0.61    inference(resolution,[],[f127,f103])).
% 1.70/0.61  fof(f103,plain,(
% 1.70/0.61    r2_hidden(sK2,sK3) | r2_hidden(sK2,sK1)),
% 1.70/0.61    inference(resolution,[],[f100,f25])).
% 1.70/0.61  fof(f25,plain,(
% 1.70/0.61    ~v3_pre_topc(sK1,sK0) | r2_hidden(sK2,sK1) | r2_hidden(sK2,sK3)),
% 1.70/0.61    inference(cnf_transformation,[],[f9])).
% 1.70/0.61  fof(f127,plain,(
% 1.70/0.61    ~r2_hidden(sK2,sK3)),
% 1.70/0.61    inference(resolution,[],[f118,f117])).
% 1.70/0.61  fof(f117,plain,(
% 1.70/0.61    r1_tarski(sK3,sK1)),
% 1.70/0.61    inference(resolution,[],[f115,f104])).
% 1.70/0.61  fof(f104,plain,(
% 1.70/0.61    r2_hidden(sK2,sK1) | r1_tarski(sK3,sK1)),
% 1.70/0.61    inference(resolution,[],[f100,f24])).
% 1.70/0.61  fof(f24,plain,(
% 1.70/0.61    ~v3_pre_topc(sK1,sK0) | r2_hidden(sK2,sK1) | r1_tarski(sK3,sK1)),
% 1.70/0.61    inference(cnf_transformation,[],[f9])).
% 1.70/0.61  fof(f118,plain,(
% 1.70/0.61    ( ! [X0] : (~r1_tarski(X0,sK1) | ~r2_hidden(sK2,X0)) )),
% 1.70/0.61    inference(resolution,[],[f115,f39])).
% 1.70/0.61  % SZS output end Proof for theBenchmark
% 1.70/0.61  % (11437)------------------------------
% 1.70/0.61  % (11437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.61  % (11437)Termination reason: Refutation
% 1.70/0.61  
% 1.70/0.61  % (11437)Memory used [KB]: 1791
% 1.70/0.61  % (11437)Time elapsed: 0.168 s
% 1.70/0.61  % (11437)------------------------------
% 1.70/0.61  % (11437)------------------------------
% 1.70/0.61  % (11430)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.70/0.61  % (11414)Success in time 0.246 s
%------------------------------------------------------------------------------
