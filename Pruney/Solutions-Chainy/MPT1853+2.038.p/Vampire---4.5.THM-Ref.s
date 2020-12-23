%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  139 (6419 expanded)
%              Number of leaves         :   18 (1637 expanded)
%              Depth                    :   35
%              Number of atoms          :  470 (35489 expanded)
%              Number of equality atoms :   57 ( 773 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f211,plain,(
    $false ),
    inference(subsumption_resolution,[],[f210,f59])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f49,f51,f50])).

% (6452)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% (6439)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% (6438)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
            & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | v1_tex_2(k1_tex_2(X0,X1),X0) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
            | ~ v1_tex_2(k1_tex_2(sK0,X1),sK0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
            | v1_tex_2(k1_tex_2(sK0,X1),sK0) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X1] :
        ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
          | ~ v1_tex_2(k1_tex_2(sK0,X1),sK0) )
        & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
          | v1_tex_2(k1_tex_2(sK0,X1),sK0) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
        | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
      & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
        | v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

fof(f210,plain,(
    ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f209,f107])).

fof(f107,plain,(
    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f106,f58])).

fof(f58,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f106,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f105,f59])).

fof(f105,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f83,f60])).

fof(f60,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f209,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f203,f167])).

fof(f167,plain,(
    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f166,f123])).

fof(f123,plain,(
    ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f122,f101])).

fof(f101,plain,(
    ~ v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f100,f58])).

fof(f100,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f99,f59])).

fof(f99,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f80,f60])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f122,plain,
    ( ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f119,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f119,plain,(
    l1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f117,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f117,plain,(
    l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f113,f59])).

fof(f113,plain,
    ( l1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f107,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f166,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    inference(resolution,[],[f164,f121])).

fof(f121,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f120,f91])).

fof(f91,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f90,f58])).

fof(f90,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f89,f74])).

fof(f89,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f65,f59])).

fof(f120,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    inference(resolution,[],[f116,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f116,plain,(
    r1_tarski(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f112,f59])).

fof(f112,plain,
    ( r1_tarski(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f107,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f164,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f163,f118])).

fof(f118,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | v1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(resolution,[],[f95,f97])).

fof(f97,plain,
    ( ~ v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(backward_demodulation,[],[f62,f94])).

fof(f94,plain,(
    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f93,f91])).

fof(f93,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f84,f60])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f62,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f95,plain,
    ( v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0))
    | v1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f92,f94])).

fof(f92,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(resolution,[],[f87,f60])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_subset_1(k6_domain_1(X0,X1),X0)
      | v1_zfmisc_1(X0) ) ),
    inference(subsumption_resolution,[],[f76,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

fof(f163,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(resolution,[],[f160,f151])).

fof(f151,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f148,f143])).

fof(f143,plain,(
    u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f142,f137])).

fof(f137,plain,
    ( u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1))
    | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f136,f59])).

fof(f136,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f133,f107])).

fof(f133,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f115,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | u1_struct_0(X0) != u1_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_tex_2(X1,X0)
          | u1_struct_0(X0) != u1_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_tex_2(X1,X0)
          | u1_struct_0(X0) != u1_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ~ ( v1_tex_2(X1,X0)
              & u1_struct_0(X0) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tex_2)).

fof(f115,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f111,f59])).

fof(f111,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f107,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | v1_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK2(X0,X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f54,f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK2(X0,X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v1_subset_1(X2,u1_struct_0(X0))
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

fof(f142,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f141,f123])).

fof(f141,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f121,f131])).

fof(f131,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f115,f118])).

fof(f148,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_zfmisc_1(u1_struct_0(sK0))
    | v1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f138,f143])).

fof(f138,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1))
    | v1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f124,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f124,plain,
    ( m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(resolution,[],[f114,f118])).

fof(f114,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f110,f59])).

fof(f110,plain,
    ( m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f107,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f160,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f159,f59])).

fof(f159,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f158,f107])).

fof(f158,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f71,f143])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f203,plain,
    ( u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f193,f72])).

fof(f193,plain,(
    v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(resolution,[],[f191,f96])).

fof(f96,plain,
    ( v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(backward_demodulation,[],[f61,f94])).

fof(f61,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f191,plain,(
    ~ v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f190,f60])).

fof(f190,plain,
    ( ~ v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(superposition,[],[f182,f94])).

fof(f182,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f181,f167])).

fof(f181,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(sK0,sK1)),X0),u1_struct_0(k1_tex_2(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f168,f119])).

fof(f168,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(sK0,sK1)),X0),u1_struct_0(k1_tex_2(sK0,sK1)))
      | ~ l1_struct_0(k1_tex_2(sK0,sK1)) ) ),
    inference(backward_demodulation,[],[f109,f167])).

fof(f109,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(sK0,sK1)),X0),u1_struct_0(k1_tex_2(sK0,sK1)))
      | ~ m1_subset_1(X0,u1_struct_0(k1_tex_2(sK0,sK1)))
      | ~ l1_struct_0(k1_tex_2(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f108,f101])).

fof(f108,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(sK0,sK1)),X0),u1_struct_0(k1_tex_2(sK0,sK1)))
      | ~ m1_subset_1(X0,u1_struct_0(k1_tex_2(sK0,sK1)))
      | ~ l1_struct_0(k1_tex_2(sK0,sK1))
      | v2_struct_0(k1_tex_2(sK0,sK1)) ) ),
    inference(resolution,[],[f104,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

fof(f104,plain,(
    v7_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f103,f58])).

fof(f103,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f102,f59])).

fof(f102,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f81,f60])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | v7_struct_0(k1_tex_2(X0,X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n013.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:24:54 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.54  % (6437)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.56  % (6437)Refutation not found, incomplete strategy% (6437)------------------------------
% 0.22/0.56  % (6437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (6462)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.56  % (6437)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (6437)Memory used [KB]: 1791
% 0.22/0.56  % (6437)Time elapsed: 0.132 s
% 0.22/0.56  % (6437)------------------------------
% 0.22/0.56  % (6437)------------------------------
% 0.22/0.57  % (6462)Refutation not found, incomplete strategy% (6462)------------------------------
% 0.22/0.57  % (6462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (6462)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (6462)Memory used [KB]: 1663
% 0.22/0.57  % (6462)Time elapsed: 0.003 s
% 0.22/0.57  % (6462)------------------------------
% 0.22/0.57  % (6462)------------------------------
% 0.22/0.57  % (6445)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.57  % (6445)Refutation not found, incomplete strategy% (6445)------------------------------
% 0.22/0.57  % (6445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (6445)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (6445)Memory used [KB]: 10618
% 0.22/0.57  % (6445)Time elapsed: 0.137 s
% 0.22/0.57  % (6445)------------------------------
% 0.22/0.57  % (6445)------------------------------
% 0.22/0.57  % (6448)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.58  % (6436)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.58  % (6442)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.59  % (6440)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.59  % (6440)Refutation found. Thanks to Tanya!
% 0.22/0.59  % SZS status Theorem for theBenchmark
% 0.22/0.59  % SZS output start Proof for theBenchmark
% 0.22/0.59  fof(f211,plain,(
% 0.22/0.59    $false),
% 0.22/0.59    inference(subsumption_resolution,[],[f210,f59])).
% 0.22/0.59  fof(f59,plain,(
% 0.22/0.59    l1_pre_topc(sK0)),
% 0.22/0.59    inference(cnf_transformation,[],[f52])).
% 0.22/0.59  fof(f52,plain,(
% 0.22/0.59    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f49,f51,f50])).
% 0.22/0.59  % (6452)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.60  % (6439)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.60  % (6438)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.61  fof(f50,plain,(
% 0.22/0.61    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X1),sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.61    introduced(choice_axiom,[])).
% 0.22/0.61  fof(f51,plain,(
% 0.22/0.61    ? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X1),sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.22/0.61    introduced(choice_axiom,[])).
% 0.22/0.61  fof(f49,plain,(
% 0.22/0.61    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.61    inference(flattening,[],[f48])).
% 0.22/0.61  fof(f48,plain,(
% 0.22/0.61    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.61    inference(nnf_transformation,[],[f22])).
% 0.22/0.61  fof(f22,plain,(
% 0.22/0.61    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.61    inference(flattening,[],[f21])).
% 0.22/0.61  fof(f21,plain,(
% 0.22/0.61    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.61    inference(ennf_transformation,[],[f18])).
% 0.22/0.61  fof(f18,negated_conjecture,(
% 0.22/0.61    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.22/0.61    inference(negated_conjecture,[],[f17])).
% 0.22/0.61  fof(f17,conjecture,(
% 0.22/0.61    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).
% 0.22/0.61  fof(f210,plain,(
% 0.22/0.61    ~l1_pre_topc(sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f209,f107])).
% 0.22/0.61  fof(f107,plain,(
% 0.22/0.61    m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f106,f58])).
% 0.22/0.61  fof(f58,plain,(
% 0.22/0.61    ~v2_struct_0(sK0)),
% 0.22/0.61    inference(cnf_transformation,[],[f52])).
% 0.22/0.61  fof(f106,plain,(
% 0.22/0.61    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f105,f59])).
% 0.22/0.61  fof(f105,plain,(
% 0.22/0.61    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.61    inference(resolution,[],[f83,f60])).
% 0.22/0.61  fof(f60,plain,(
% 0.22/0.61    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.61    inference(cnf_transformation,[],[f52])).
% 0.22/0.61  fof(f83,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | m1_pre_topc(k1_tex_2(X0,X1),X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f45])).
% 0.22/0.61  fof(f45,plain,(
% 0.22/0.61    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.61    inference(flattening,[],[f44])).
% 0.22/0.61  fof(f44,plain,(
% 0.22/0.61    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.61    inference(ennf_transformation,[],[f20])).
% 0.22/0.61  fof(f20,plain,(
% 0.22/0.61    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.22/0.61    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.61  fof(f11,axiom,(
% 0.22/0.61    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.22/0.61  fof(f209,plain,(
% 0.22/0.61    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f203,f167])).
% 0.22/0.61  fof(f167,plain,(
% 0.22/0.61    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.61    inference(subsumption_resolution,[],[f166,f123])).
% 0.22/0.61  fof(f123,plain,(
% 0.22/0.61    ~v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.22/0.61    inference(subsumption_resolution,[],[f122,f101])).
% 0.22/0.61  fof(f101,plain,(
% 0.22/0.61    ~v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.61    inference(subsumption_resolution,[],[f100,f58])).
% 0.22/0.61  fof(f100,plain,(
% 0.22/0.61    ~v2_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f99,f59])).
% 0.22/0.61  fof(f99,plain,(
% 0.22/0.61    ~v2_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.61    inference(resolution,[],[f80,f60])).
% 0.22/0.61  fof(f80,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_struct_0(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f43])).
% 0.22/0.61  fof(f43,plain,(
% 0.22/0.61    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.61    inference(flattening,[],[f42])).
% 0.22/0.61  fof(f42,plain,(
% 0.22/0.61    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.61    inference(ennf_transformation,[],[f19])).
% 0.22/0.61  fof(f19,plain,(
% 0.22/0.61    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.22/0.61    inference(pure_predicate_removal,[],[f12])).
% 0.22/0.61  fof(f12,axiom,(
% 0.22/0.61    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).
% 0.22/0.61  fof(f122,plain,(
% 0.22/0.61    ~v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.61    inference(resolution,[],[f119,f74])).
% 0.22/0.61  fof(f74,plain,(
% 0.22/0.61    ( ! [X0] : (~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f34])).
% 0.22/0.61  fof(f34,plain,(
% 0.22/0.61    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.61    inference(flattening,[],[f33])).
% 0.22/0.61  fof(f33,plain,(
% 0.22/0.61    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.61    inference(ennf_transformation,[],[f6])).
% 0.22/0.61  fof(f6,axiom,(
% 0.22/0.61    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.61  fof(f119,plain,(
% 0.22/0.61    l1_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.61    inference(resolution,[],[f117,f65])).
% 0.22/0.61  fof(f65,plain,(
% 0.22/0.61    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f25])).
% 0.22/0.61  fof(f25,plain,(
% 0.22/0.61    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.61    inference(ennf_transformation,[],[f3])).
% 0.22/0.61  fof(f3,axiom,(
% 0.22/0.61    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.61  fof(f117,plain,(
% 0.22/0.61    l1_pre_topc(k1_tex_2(sK0,sK1))),
% 0.22/0.61    inference(subsumption_resolution,[],[f113,f59])).
% 0.22/0.61  fof(f113,plain,(
% 0.22/0.61    l1_pre_topc(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.22/0.61    inference(resolution,[],[f107,f66])).
% 0.22/0.61  fof(f66,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f26])).
% 0.22/0.61  fof(f26,plain,(
% 0.22/0.61    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.61    inference(ennf_transformation,[],[f4])).
% 0.22/0.61  fof(f4,axiom,(
% 0.22/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.61  fof(f166,plain,(
% 0.22/0.61    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.22/0.61    inference(duplicate_literal_removal,[],[f165])).
% 0.22/0.61  fof(f165,plain,(
% 0.22/0.61    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.22/0.61    inference(resolution,[],[f164,f121])).
% 0.22/0.61  fof(f121,plain,(
% 0.22/0.61    ~v1_zfmisc_1(u1_struct_0(sK0)) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.22/0.61    inference(subsumption_resolution,[],[f120,f91])).
% 0.22/0.61  fof(f91,plain,(
% 0.22/0.61    ~v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.61    inference(subsumption_resolution,[],[f90,f58])).
% 0.22/0.61  fof(f90,plain,(
% 0.22/0.61    ~v1_xboole_0(u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.22/0.61    inference(resolution,[],[f89,f74])).
% 0.22/0.61  fof(f89,plain,(
% 0.22/0.61    l1_struct_0(sK0)),
% 0.22/0.61    inference(resolution,[],[f65,f59])).
% 0.22/0.61  fof(f120,plain,(
% 0.22/0.61    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~v1_zfmisc_1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.22/0.61    inference(resolution,[],[f116,f64])).
% 0.22/0.61  fof(f64,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f24])).
% 0.22/0.61  fof(f24,plain,(
% 0.22/0.61    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.61    inference(flattening,[],[f23])).
% 0.22/0.61  fof(f23,plain,(
% 0.22/0.61    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.22/0.61    inference(ennf_transformation,[],[f14])).
% 0.22/0.61  fof(f14,axiom,(
% 0.22/0.61    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 0.22/0.61  fof(f116,plain,(
% 0.22/0.61    r1_tarski(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 0.22/0.61    inference(subsumption_resolution,[],[f112,f59])).
% 0.22/0.61  fof(f112,plain,(
% 0.22/0.61    r1_tarski(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.22/0.61    inference(resolution,[],[f107,f67])).
% 0.22/0.61  fof(f67,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f27])).
% 0.22/0.61  fof(f27,plain,(
% 0.22/0.61    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.61    inference(ennf_transformation,[],[f8])).
% 0.22/0.61  fof(f8,axiom,(
% 0.22/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.22/0.61  fof(f164,plain,(
% 0.22/0.61    v1_zfmisc_1(u1_struct_0(sK0)) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.61    inference(subsumption_resolution,[],[f163,f118])).
% 0.22/0.61  fof(f118,plain,(
% 0.22/0.61    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | v1_zfmisc_1(u1_struct_0(sK0))),
% 0.22/0.61    inference(resolution,[],[f95,f97])).
% 0.22/0.61  fof(f97,plain,(
% 0.22/0.61    ~v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.61    inference(backward_demodulation,[],[f62,f94])).
% 0.22/0.61  fof(f94,plain,(
% 0.22/0.61    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)),
% 0.22/0.61    inference(subsumption_resolution,[],[f93,f91])).
% 0.22/0.61  fof(f93,plain,(
% 0.22/0.61    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) | v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.61    inference(resolution,[],[f84,f60])).
% 0.22/0.61  fof(f84,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f47])).
% 0.22/0.61  fof(f47,plain,(
% 0.22/0.61    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.61    inference(flattening,[],[f46])).
% 0.22/0.61  fof(f46,plain,(
% 0.22/0.61    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.61    inference(ennf_transformation,[],[f7])).
% 0.22/0.61  fof(f7,axiom,(
% 0.22/0.61    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.61  fof(f62,plain,(
% 0.22/0.61    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.61    inference(cnf_transformation,[],[f52])).
% 0.22/0.61  fof(f95,plain,(
% 0.22/0.61    v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0)) | v1_zfmisc_1(u1_struct_0(sK0))),
% 0.22/0.61    inference(backward_demodulation,[],[f92,f94])).
% 0.22/0.61  fof(f92,plain,(
% 0.22/0.61    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_zfmisc_1(u1_struct_0(sK0))),
% 0.22/0.61    inference(resolution,[],[f87,f60])).
% 0.22/0.61  fof(f87,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_subset_1(k6_domain_1(X0,X1),X0) | v1_zfmisc_1(X0)) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f76,f73])).
% 0.22/0.61  fof(f73,plain,(
% 0.22/0.61    ( ! [X0] : (~v1_xboole_0(X0) | v1_zfmisc_1(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f32])).
% 0.22/0.61  fof(f32,plain,(
% 0.22/0.61    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.61    inference(ennf_transformation,[],[f2])).
% 0.22/0.61  fof(f2,axiom,(
% 0.22/0.61    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).
% 0.22/0.61  fof(f76,plain,(
% 0.22/0.61    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f38])).
% 0.22/0.61  fof(f38,plain,(
% 0.22/0.61    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.22/0.61    inference(flattening,[],[f37])).
% 0.22/0.61  fof(f37,plain,(
% 0.22/0.61    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.22/0.61    inference(ennf_transformation,[],[f15])).
% 0.22/0.61  fof(f15,axiom,(
% 0.22/0.61    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).
% 0.22/0.61  fof(f163,plain,(
% 0.22/0.61    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v1_zfmisc_1(u1_struct_0(sK0))),
% 0.22/0.61    inference(resolution,[],[f160,f151])).
% 0.22/0.61  fof(f151,plain,(
% 0.22/0.61    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v1_zfmisc_1(u1_struct_0(sK0))),
% 0.22/0.61    inference(forward_demodulation,[],[f148,f143])).
% 0.22/0.61  fof(f143,plain,(
% 0.22/0.61    u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))),
% 0.22/0.61    inference(subsumption_resolution,[],[f142,f137])).
% 0.22/0.61  fof(f137,plain,(
% 0.22/0.61    u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1)) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))),
% 0.22/0.61    inference(subsumption_resolution,[],[f136,f59])).
% 0.22/0.61  fof(f136,plain,(
% 0.22/0.61    u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f133,f107])).
% 0.22/0.61  fof(f133,plain,(
% 0.22/0.61    u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.61    inference(resolution,[],[f115,f72])).
% 0.22/0.61  fof(f72,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | u1_struct_0(X0) != u1_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f31])).
% 0.22/0.61  fof(f31,plain,(
% 0.22/0.61    ! [X0] : (! [X1] : (~v1_tex_2(X1,X0) | u1_struct_0(X0) != u1_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.61    inference(flattening,[],[f30])).
% 0.22/0.61  fof(f30,plain,(
% 0.22/0.61    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) | u1_struct_0(X0) != u1_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.61    inference(ennf_transformation,[],[f13])).
% 0.22/0.61  fof(f13,axiom,(
% 0.22/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ~(v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1))))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tex_2)).
% 0.22/0.61  fof(f115,plain,(
% 0.22/0.61    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))),
% 0.22/0.61    inference(subsumption_resolution,[],[f111,f59])).
% 0.22/0.61  fof(f111,plain,(
% 0.22/0.61    u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.61    inference(resolution,[],[f107,f70])).
% 0.22/0.61  fof(f70,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | v1_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f56])).
% 0.22/0.61  fof(f56,plain,(
% 0.22/0.61    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f54,f55])).
% 0.22/0.61  fof(f55,plain,(
% 0.22/0.61    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.61    introduced(choice_axiom,[])).
% 0.22/0.61  fof(f54,plain,(
% 0.22/0.61    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.61    inference(rectify,[],[f53])).
% 0.22/0.61  fof(f53,plain,(
% 0.22/0.61    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.61    inference(nnf_transformation,[],[f29])).
% 0.22/0.61  fof(f29,plain,(
% 0.22/0.61    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.61    inference(flattening,[],[f28])).
% 0.22/0.61  fof(f28,plain,(
% 0.22/0.61    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.61    inference(ennf_transformation,[],[f9])).
% 0.22/0.61  fof(f9,axiom,(
% 0.22/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).
% 0.22/0.61  fof(f142,plain,(
% 0.22/0.61    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))),
% 0.22/0.61    inference(subsumption_resolution,[],[f141,f123])).
% 0.22/0.61  fof(f141,plain,(
% 0.22/0.61    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))),
% 0.22/0.61    inference(resolution,[],[f121,f131])).
% 0.22/0.61  fof(f131,plain,(
% 0.22/0.61    v1_zfmisc_1(u1_struct_0(sK0)) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))),
% 0.22/0.61    inference(resolution,[],[f115,f118])).
% 0.22/0.61  fof(f148,plain,(
% 0.22/0.61    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v1_zfmisc_1(u1_struct_0(sK0)) | v1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 0.22/0.61    inference(backward_demodulation,[],[f138,f143])).
% 0.22/0.61  fof(f138,plain,(
% 0.22/0.61    v1_zfmisc_1(u1_struct_0(sK0)) | u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1)) | v1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 0.22/0.61    inference(resolution,[],[f124,f79])).
% 0.22/0.61  fof(f79,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f57])).
% 0.22/0.61  fof(f57,plain,(
% 0.22/0.61    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.61    inference(nnf_transformation,[],[f41])).
% 0.22/0.61  fof(f41,plain,(
% 0.22/0.61    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.61    inference(ennf_transformation,[],[f10])).
% 0.22/0.61  fof(f10,axiom,(
% 0.22/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.22/0.61  fof(f124,plain,(
% 0.22/0.61    m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(u1_struct_0(sK0))),
% 0.22/0.61    inference(resolution,[],[f114,f118])).
% 0.22/0.61  fof(f114,plain,(
% 0.22/0.61    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.61    inference(subsumption_resolution,[],[f110,f59])).
% 0.22/0.61  fof(f110,plain,(
% 0.22/0.61    m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.61    inference(resolution,[],[f107,f69])).
% 0.22/0.61  fof(f69,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f56])).
% 0.22/0.61  fof(f160,plain,(
% 0.22/0.61    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f159,f59])).
% 0.22/0.61  fof(f159,plain,(
% 0.22/0.61    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f158,f107])).
% 0.22/0.61  fof(f158,plain,(
% 0.22/0.61    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.61    inference(superposition,[],[f71,f143])).
% 0.22/0.61  fof(f71,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f56])).
% 0.22/0.61  fof(f203,plain,(
% 0.22/0.61    u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.61    inference(resolution,[],[f193,f72])).
% 0.22/0.61  fof(f193,plain,(
% 0.22/0.61    v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.61    inference(resolution,[],[f191,f96])).
% 0.22/0.61  fof(f96,plain,(
% 0.22/0.61    v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.61    inference(backward_demodulation,[],[f61,f94])).
% 0.22/0.61  fof(f61,plain,(
% 0.22/0.61    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.61    inference(cnf_transformation,[],[f52])).
% 0.22/0.61  fof(f191,plain,(
% 0.22/0.61    ~v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0))),
% 0.22/0.61    inference(subsumption_resolution,[],[f190,f60])).
% 0.22/0.61  fof(f190,plain,(
% 0.22/0.61    ~v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.61    inference(superposition,[],[f182,f94])).
% 0.22/0.61  fof(f182,plain,(
% 0.22/0.61    ( ! [X0] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.22/0.61    inference(forward_demodulation,[],[f181,f167])).
% 0.22/0.61  fof(f181,plain,(
% 0.22/0.61    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(sK0,sK1)),X0),u1_struct_0(k1_tex_2(sK0,sK1)))) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f168,f119])).
% 0.22/0.61  fof(f168,plain,(
% 0.22/0.61    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(sK0,sK1)),X0),u1_struct_0(k1_tex_2(sK0,sK1))) | ~l1_struct_0(k1_tex_2(sK0,sK1))) )),
% 0.22/0.61    inference(backward_demodulation,[],[f109,f167])).
% 0.22/0.61  fof(f109,plain,(
% 0.22/0.61    ( ! [X0] : (~v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(sK0,sK1)),X0),u1_struct_0(k1_tex_2(sK0,sK1))) | ~m1_subset_1(X0,u1_struct_0(k1_tex_2(sK0,sK1))) | ~l1_struct_0(k1_tex_2(sK0,sK1))) )),
% 0.22/0.61    inference(subsumption_resolution,[],[f108,f101])).
% 0.22/0.61  fof(f108,plain,(
% 0.22/0.61    ( ! [X0] : (~v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(sK0,sK1)),X0),u1_struct_0(k1_tex_2(sK0,sK1))) | ~m1_subset_1(X0,u1_struct_0(k1_tex_2(sK0,sK1))) | ~l1_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1))) )),
% 0.22/0.61    inference(resolution,[],[f104,f75])).
% 0.22/0.61  fof(f75,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f36])).
% 0.22/0.61  fof(f36,plain,(
% 0.22/0.61    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.61    inference(flattening,[],[f35])).
% 0.22/0.61  fof(f35,plain,(
% 0.22/0.61    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.61    inference(ennf_transformation,[],[f16])).
% 0.22/0.61  fof(f16,axiom,(
% 0.22/0.61    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).
% 0.22/0.61  fof(f104,plain,(
% 0.22/0.61    v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.61    inference(subsumption_resolution,[],[f103,f58])).
% 0.22/0.61  fof(f103,plain,(
% 0.22/0.61    v7_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0)),
% 0.22/0.61    inference(subsumption_resolution,[],[f102,f59])).
% 0.22/0.61  fof(f102,plain,(
% 0.22/0.61    v7_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.61    inference(resolution,[],[f81,f60])).
% 0.22/0.61  fof(f81,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | v7_struct_0(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f43])).
% 0.22/0.61  % SZS output end Proof for theBenchmark
% 0.22/0.61  % (6440)------------------------------
% 0.22/0.61  % (6440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.61  % (6440)Termination reason: Refutation
% 0.22/0.61  
% 0.22/0.61  % (6440)Memory used [KB]: 1791
% 0.22/0.61  % (6440)Time elapsed: 0.105 s
% 0.22/0.61  % (6440)------------------------------
% 0.22/0.61  % (6440)------------------------------
% 0.22/0.61  % (6432)Success in time 0.244 s
%------------------------------------------------------------------------------
