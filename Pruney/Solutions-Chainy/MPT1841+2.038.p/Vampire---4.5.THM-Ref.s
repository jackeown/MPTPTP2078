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
% DateTime   : Thu Dec  3 13:20:14 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 168 expanded)
%              Number of leaves         :   11 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :  158 ( 609 expanded)
%              Number of equality atoms :   19 (  29 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f151,plain,(
    $false ),
    inference(subsumption_resolution,[],[f150,f76])).

fof(f76,plain,(
    v1_subset_1(sK0,sK0) ),
    inference(backward_demodulation,[],[f61,f74])).

fof(f74,plain,(
    sK0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f73,f48])).

fof(f48,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f73,plain,
    ( sK0 = k1_tarski(sK1)
    | v1_xboole_0(k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f72,f33])).

fof(f33,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK0)
          & v1_subset_1(k6_domain_1(sK0,X1),sK0)
          & m1_subset_1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f72,plain,
    ( sK0 = k1_tarski(sK1)
    | v1_xboole_0(sK0)
    | v1_xboole_0(k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f71,f36])).

fof(f36,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,
    ( sK0 = k1_tarski(sK1)
    | ~ v1_zfmisc_1(sK0)
    | v1_xboole_0(sK0)
    | v1_xboole_0(k1_tarski(sK1)) ),
    inference(resolution,[],[f64,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f64,plain,(
    r1_tarski(k1_tarski(sK1),sK0) ),
    inference(resolution,[],[f63,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f63,plain,(
    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f62,f60])).

fof(f60,plain,(
    k6_domain_1(sK0,sK1) = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f58,f33])).

fof(f58,plain,
    ( k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f34,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f34,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f59,f33])).

fof(f59,plain,
    ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f34,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f61,plain,(
    v1_subset_1(k1_tarski(sK1),sK0) ),
    inference(backward_demodulation,[],[f35,f60])).

fof(f35,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f150,plain,(
    ~ v1_subset_1(sK0,sK0) ),
    inference(superposition,[],[f39,f136])).

fof(f136,plain,(
    sK0 = sK2(sK0) ),
    inference(subsumption_resolution,[],[f135,f38])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK2(X0),X0)
      & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

fof(f135,plain,
    ( sK0 = sK2(sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f107,f43])).

fof(f107,plain,
    ( ~ r1_tarski(sK2(sK0),sK0)
    | sK0 = sK2(sK0) ),
    inference(resolution,[],[f106,f56])).

fof(f56,plain,(
    ! [X4] :
      ( v1_xboole_0(X4)
      | ~ r1_tarski(X4,sK0)
      | sK0 = X4 ) ),
    inference(subsumption_resolution,[],[f55,f36])).

fof(f55,plain,(
    ! [X4] :
      ( sK0 = X4
      | ~ r1_tarski(X4,sK0)
      | ~ v1_zfmisc_1(sK0)
      | v1_xboole_0(X4) ) ),
    inference(resolution,[],[f33,f37])).

fof(f106,plain,(
    ~ v1_xboole_0(sK2(sK0)) ),
    inference(subsumption_resolution,[],[f105,f38])).

fof(f105,plain,
    ( ~ v1_xboole_0(sK2(sK0))
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f53,f39])).

fof(f53,plain,(
    ! [X2] :
      ( v1_subset_1(X2,sK0)
      | ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f33,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_subset_1(X1,X0)
           => ~ v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_subset_1)).

fof(f39,plain,(
    ! [X0] : ~ v1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:02:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.23/0.50  % (26171)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.23/0.51  % (26187)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.23/0.53  % (26195)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.23/0.53  % (26187)Refutation not found, incomplete strategy% (26187)------------------------------
% 0.23/0.53  % (26187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (26187)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (26187)Memory used [KB]: 10618
% 0.23/0.53  % (26187)Time elapsed: 0.116 s
% 0.23/0.53  % (26187)------------------------------
% 0.23/0.53  % (26187)------------------------------
% 0.23/0.53  % (26173)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.53  % (26172)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.53  % (26172)Refutation not found, incomplete strategy% (26172)------------------------------
% 0.23/0.53  % (26172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (26172)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (26172)Memory used [KB]: 10618
% 0.23/0.53  % (26172)Time elapsed: 0.114 s
% 0.23/0.53  % (26172)------------------------------
% 0.23/0.53  % (26172)------------------------------
% 0.23/0.54  % (26199)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.23/0.54  % (26186)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.23/0.54  % (26175)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.54  % (26170)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.23/0.54  % (26176)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.54  % (26170)Refutation found. Thanks to Tanya!
% 0.23/0.54  % SZS status Theorem for theBenchmark
% 0.23/0.54  % SZS output start Proof for theBenchmark
% 0.23/0.54  fof(f151,plain,(
% 0.23/0.54    $false),
% 0.23/0.54    inference(subsumption_resolution,[],[f150,f76])).
% 0.23/0.54  fof(f76,plain,(
% 0.23/0.54    v1_subset_1(sK0,sK0)),
% 0.23/0.54    inference(backward_demodulation,[],[f61,f74])).
% 0.23/0.54  fof(f74,plain,(
% 0.23/0.54    sK0 = k1_tarski(sK1)),
% 0.23/0.54    inference(subsumption_resolution,[],[f73,f48])).
% 0.23/0.54  fof(f48,plain,(
% 0.23/0.54    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f6])).
% 0.23/0.54  fof(f6,axiom,(
% 0.23/0.54    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.23/0.54  fof(f73,plain,(
% 0.23/0.54    sK0 = k1_tarski(sK1) | v1_xboole_0(k1_tarski(sK1))),
% 0.23/0.54    inference(subsumption_resolution,[],[f72,f33])).
% 0.23/0.54  fof(f33,plain,(
% 0.23/0.54    ~v1_xboole_0(sK0)),
% 0.23/0.54    inference(cnf_transformation,[],[f27])).
% 0.23/0.54  fof(f27,plain,(
% 0.23/0.54    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.23/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f26,f25])).
% 0.23/0.54  fof(f25,plain,(
% 0.23/0.54    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.23/0.54    introduced(choice_axiom,[])).
% 0.23/0.54  fof(f26,plain,(
% 0.23/0.54    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.23/0.54    introduced(choice_axiom,[])).
% 0.23/0.54  fof(f16,plain,(
% 0.23/0.54    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.23/0.54    inference(flattening,[],[f15])).
% 0.23/0.54  fof(f15,plain,(
% 0.23/0.54    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.23/0.54    inference(ennf_transformation,[],[f14])).
% 0.23/0.54  fof(f14,negated_conjecture,(
% 0.23/0.54    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.23/0.54    inference(negated_conjecture,[],[f13])).
% 0.23/0.54  fof(f13,conjecture,(
% 0.23/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 0.23/0.54  fof(f72,plain,(
% 0.23/0.54    sK0 = k1_tarski(sK1) | v1_xboole_0(sK0) | v1_xboole_0(k1_tarski(sK1))),
% 0.23/0.54    inference(subsumption_resolution,[],[f71,f36])).
% 0.23/0.54  fof(f36,plain,(
% 0.23/0.54    v1_zfmisc_1(sK0)),
% 0.23/0.54    inference(cnf_transformation,[],[f27])).
% 0.23/0.54  fof(f71,plain,(
% 0.23/0.54    sK0 = k1_tarski(sK1) | ~v1_zfmisc_1(sK0) | v1_xboole_0(sK0) | v1_xboole_0(k1_tarski(sK1))),
% 0.23/0.54    inference(resolution,[],[f64,f37])).
% 0.23/0.54  fof(f37,plain,(
% 0.23/0.54    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f18])).
% 0.23/0.54  fof(f18,plain,(
% 0.23/0.54    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.23/0.54    inference(flattening,[],[f17])).
% 0.23/0.54  fof(f17,plain,(
% 0.23/0.54    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.23/0.54    inference(ennf_transformation,[],[f12])).
% 0.23/0.54  fof(f12,axiom,(
% 0.23/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 0.23/0.54  fof(f64,plain,(
% 0.23/0.54    r1_tarski(k1_tarski(sK1),sK0)),
% 0.23/0.54    inference(resolution,[],[f63,f43])).
% 0.23/0.54  fof(f43,plain,(
% 0.23/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f30])).
% 0.23/0.54  fof(f30,plain,(
% 0.23/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.23/0.54    inference(nnf_transformation,[],[f9])).
% 0.23/0.54  fof(f9,axiom,(
% 0.23/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.23/0.54  fof(f63,plain,(
% 0.23/0.54    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))),
% 0.23/0.54    inference(forward_demodulation,[],[f62,f60])).
% 0.23/0.54  fof(f60,plain,(
% 0.23/0.54    k6_domain_1(sK0,sK1) = k1_tarski(sK1)),
% 0.23/0.54    inference(subsumption_resolution,[],[f58,f33])).
% 0.23/0.54  fof(f58,plain,(
% 0.23/0.54    k6_domain_1(sK0,sK1) = k1_tarski(sK1) | v1_xboole_0(sK0)),
% 0.23/0.54    inference(resolution,[],[f34,f42])).
% 0.23/0.54  fof(f42,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f24])).
% 0.23/0.54  fof(f24,plain,(
% 0.23/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.23/0.54    inference(flattening,[],[f23])).
% 0.23/0.54  fof(f23,plain,(
% 0.23/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.23/0.54    inference(ennf_transformation,[],[f11])).
% 0.23/0.54  fof(f11,axiom,(
% 0.23/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.23/0.54  fof(f34,plain,(
% 0.23/0.54    m1_subset_1(sK1,sK0)),
% 0.23/0.54    inference(cnf_transformation,[],[f27])).
% 0.23/0.54  fof(f62,plain,(
% 0.23/0.54    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.23/0.54    inference(subsumption_resolution,[],[f59,f33])).
% 0.23/0.54  fof(f59,plain,(
% 0.23/0.54    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(sK0)),
% 0.23/0.54    inference(resolution,[],[f34,f41])).
% 0.23/0.54  fof(f41,plain,(
% 0.23/0.54    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f22])).
% 0.23/0.54  fof(f22,plain,(
% 0.23/0.54    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.23/0.54    inference(flattening,[],[f21])).
% 0.23/0.54  fof(f21,plain,(
% 0.23/0.54    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.23/0.54    inference(ennf_transformation,[],[f10])).
% 0.23/0.54  fof(f10,axiom,(
% 0.23/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.23/0.54  fof(f61,plain,(
% 0.23/0.54    v1_subset_1(k1_tarski(sK1),sK0)),
% 0.23/0.54    inference(backward_demodulation,[],[f35,f60])).
% 0.23/0.54  fof(f35,plain,(
% 0.23/0.54    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.23/0.54    inference(cnf_transformation,[],[f27])).
% 0.23/0.54  fof(f150,plain,(
% 0.23/0.54    ~v1_subset_1(sK0,sK0)),
% 0.23/0.54    inference(superposition,[],[f39,f136])).
% 0.23/0.54  fof(f136,plain,(
% 0.23/0.54    sK0 = sK2(sK0)),
% 0.23/0.54    inference(subsumption_resolution,[],[f135,f38])).
% 0.23/0.54  fof(f38,plain,(
% 0.23/0.54    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(X0))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f29])).
% 0.23/0.54  fof(f29,plain,(
% 0.23/0.54    ! [X0] : (~v1_subset_1(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)))),
% 0.23/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f28])).
% 0.23/0.54  fof(f28,plain,(
% 0.23/0.54    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(X0))))),
% 0.23/0.54    introduced(choice_axiom,[])).
% 0.23/0.54  fof(f8,axiom,(
% 0.23/0.54    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).
% 0.23/0.54  fof(f135,plain,(
% 0.23/0.54    sK0 = sK2(sK0) | ~m1_subset_1(sK2(sK0),k1_zfmisc_1(sK0))),
% 0.23/0.54    inference(resolution,[],[f107,f43])).
% 0.23/0.54  fof(f107,plain,(
% 0.23/0.54    ~r1_tarski(sK2(sK0),sK0) | sK0 = sK2(sK0)),
% 0.23/0.54    inference(resolution,[],[f106,f56])).
% 0.23/0.54  fof(f56,plain,(
% 0.23/0.54    ( ! [X4] : (v1_xboole_0(X4) | ~r1_tarski(X4,sK0) | sK0 = X4) )),
% 0.23/0.54    inference(subsumption_resolution,[],[f55,f36])).
% 0.23/0.54  fof(f55,plain,(
% 0.23/0.54    ( ! [X4] : (sK0 = X4 | ~r1_tarski(X4,sK0) | ~v1_zfmisc_1(sK0) | v1_xboole_0(X4)) )),
% 0.23/0.54    inference(resolution,[],[f33,f37])).
% 0.23/0.54  fof(f106,plain,(
% 0.23/0.54    ~v1_xboole_0(sK2(sK0))),
% 0.23/0.54    inference(subsumption_resolution,[],[f105,f38])).
% 0.23/0.54  fof(f105,plain,(
% 0.23/0.54    ~v1_xboole_0(sK2(sK0)) | ~m1_subset_1(sK2(sK0),k1_zfmisc_1(sK0))),
% 0.23/0.54    inference(resolution,[],[f53,f39])).
% 0.23/0.54  fof(f53,plain,(
% 0.23/0.54    ( ! [X2] : (v1_subset_1(X2,sK0) | ~v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(sK0))) )),
% 0.23/0.54    inference(resolution,[],[f33,f40])).
% 0.23/0.54  fof(f40,plain,(
% 0.23/0.54    ( ! [X0,X1] : (~v1_xboole_0(X1) | v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f20])).
% 0.23/0.54  fof(f20,plain,(
% 0.23/0.54    ! [X0] : (! [X1] : (~v1_xboole_0(X1) | v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.23/0.54    inference(flattening,[],[f19])).
% 0.23/0.54  fof(f19,plain,(
% 0.23/0.54    ! [X0] : (! [X1] : ((~v1_xboole_0(X1) | v1_subset_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.23/0.54    inference(ennf_transformation,[],[f7])).
% 0.23/0.54  fof(f7,axiom,(
% 0.23/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_subset_1(X1,X0) => ~v1_xboole_0(X1))))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_subset_1)).
% 0.23/0.54  fof(f39,plain,(
% 0.23/0.54    ( ! [X0] : (~v1_subset_1(sK2(X0),X0)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f29])).
% 0.23/0.54  % SZS output end Proof for theBenchmark
% 0.23/0.54  % (26170)------------------------------
% 0.23/0.54  % (26170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (26170)Termination reason: Refutation
% 0.23/0.54  
% 0.23/0.54  % (26170)Memory used [KB]: 1791
% 0.23/0.54  % (26170)Time elapsed: 0.125 s
% 0.23/0.54  % (26170)------------------------------
% 0.23/0.54  % (26170)------------------------------
% 0.23/0.54  % (26189)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.23/0.54  % (26169)Success in time 0.173 s
%------------------------------------------------------------------------------
