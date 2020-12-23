%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:16 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 132 expanded)
%              Number of leaves         :   17 (  40 expanded)
%              Depth                    :   15
%              Number of atoms          :  184 ( 377 expanded)
%              Number of equality atoms :   42 (  63 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f101,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f66,f99,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f99,plain,(
    r2_hidden(sK1,sK1) ),
    inference(forward_demodulation,[],[f97,f61])).

fof(f61,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f39,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

% (15851)Refutation not found, incomplete strategy% (15851)------------------------------
% (15851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15851)Termination reason: Refutation not found, incomplete strategy

% (15851)Memory used [KB]: 10618
% (15851)Time elapsed: 0.102 s
% (15851)------------------------------
% (15851)------------------------------
fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f39,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f97,plain,(
    r2_hidden(sK1,k3_tarski(k2_enumset1(sK1,sK1,sK1,k1_xboole_0))) ),
    inference(superposition,[],[f68,f90])).

fof(f90,plain,(
    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(forward_demodulation,[],[f89,f78])).

fof(f78,plain,(
    k1_xboole_0 = k6_domain_1(sK0,sK1) ),
    inference(resolution,[],[f76,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f76,plain,(
    v1_xboole_0(k6_domain_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f75,f35])).

fof(f35,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f29,f28])).

fof(f28,plain,
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

fof(f29,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

% (15845)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
fof(f15,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f75,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f74,f36])).

fof(f36,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f72,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

% (15847)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f72,plain,
    ( ~ m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(k6_domain_1(sK0,sK1)) ),
    inference(resolution,[],[f71,f37])).

fof(f37,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_subset_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f69,f38])).

fof(f38,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f44,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

% (15850)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f89,plain,(
    k6_domain_1(sK0,sK1) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f87,f35])).

fof(f87,plain,
    ( k6_domain_1(sK0,sK1) = k2_enumset1(sK1,sK1,sK1,sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f62,f36])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_enumset1(X1,X1,X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f47,f59])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f57])).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f68,plain,(
    ! [X1] : r2_hidden(X1,k3_tarski(k2_enumset1(X1,X1,X1,k2_enumset1(X1,X1,X1,X1)))) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k3_tarski(k2_enumset1(X1,X1,X1,k2_enumset1(X1,X1,X1,X1))))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f54,f60])).

fof(f60,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f41,f58,f59])).

% (15843)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
fof(f41,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 20:59:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.51  % (15851)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.23/0.52  % (15864)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.23/0.52  % (15863)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.23/0.52  % (15855)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.23/0.53  % (15863)Refutation found. Thanks to Tanya!
% 0.23/0.53  % SZS status Theorem for theBenchmark
% 0.23/0.53  % (15856)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.23/0.53  % SZS output start Proof for theBenchmark
% 0.23/0.53  fof(f101,plain,(
% 0.23/0.53    $false),
% 0.23/0.53    inference(unit_resulting_resolution,[],[f66,f99,f55])).
% 0.23/0.53  fof(f55,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f27])).
% 0.23/0.53  fof(f27,plain,(
% 0.23/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.23/0.53    inference(ennf_transformation,[],[f11])).
% 0.23/0.53  fof(f11,axiom,(
% 0.23/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.23/0.53  fof(f99,plain,(
% 0.23/0.53    r2_hidden(sK1,sK1)),
% 0.23/0.53    inference(forward_demodulation,[],[f97,f61])).
% 0.23/0.53  fof(f61,plain,(
% 0.23/0.53    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0) )),
% 0.23/0.53    inference(definition_unfolding,[],[f39,f58])).
% 0.23/0.53  fof(f58,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.23/0.53    inference(definition_unfolding,[],[f45,f57])).
% 0.23/0.53  fof(f57,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.23/0.53    inference(definition_unfolding,[],[f46,f56])).
% 0.23/0.53  fof(f56,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f6])).
% 0.23/0.53  fof(f6,axiom,(
% 0.23/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.23/0.53  fof(f46,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f5])).
% 0.23/0.53  % (15851)Refutation not found, incomplete strategy% (15851)------------------------------
% 0.23/0.53  % (15851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (15851)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (15851)Memory used [KB]: 10618
% 0.23/0.53  % (15851)Time elapsed: 0.102 s
% 0.23/0.53  % (15851)------------------------------
% 0.23/0.53  % (15851)------------------------------
% 0.23/0.53  fof(f5,axiom,(
% 0.23/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.23/0.53  fof(f45,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f7])).
% 0.23/0.53  fof(f7,axiom,(
% 0.23/0.53    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.23/0.53  fof(f39,plain,(
% 0.23/0.53    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.53    inference(cnf_transformation,[],[f3])).
% 0.23/0.53  fof(f3,axiom,(
% 0.23/0.53    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.23/0.53  fof(f97,plain,(
% 0.23/0.53    r2_hidden(sK1,k3_tarski(k2_enumset1(sK1,sK1,sK1,k1_xboole_0)))),
% 0.23/0.53    inference(superposition,[],[f68,f90])).
% 0.23/0.53  fof(f90,plain,(
% 0.23/0.53    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.23/0.53    inference(forward_demodulation,[],[f89,f78])).
% 0.23/0.53  fof(f78,plain,(
% 0.23/0.53    k1_xboole_0 = k6_domain_1(sK0,sK1)),
% 0.23/0.53    inference(resolution,[],[f76,f42])).
% 0.23/0.53  fof(f42,plain,(
% 0.23/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.23/0.53    inference(cnf_transformation,[],[f19])).
% 0.23/0.53  fof(f19,plain,(
% 0.23/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.23/0.53    inference(ennf_transformation,[],[f1])).
% 0.23/0.53  fof(f1,axiom,(
% 0.23/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.23/0.53  fof(f76,plain,(
% 0.23/0.53    v1_xboole_0(k6_domain_1(sK0,sK1))),
% 0.23/0.53    inference(subsumption_resolution,[],[f75,f35])).
% 0.23/0.53  fof(f35,plain,(
% 0.23/0.53    ~v1_xboole_0(sK0)),
% 0.23/0.53    inference(cnf_transformation,[],[f30])).
% 0.23/0.53  fof(f30,plain,(
% 0.23/0.53    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.23/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f29,f28])).
% 0.23/0.53  fof(f28,plain,(
% 0.23/0.53    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.23/0.53    introduced(choice_axiom,[])).
% 0.23/0.53  fof(f29,plain,(
% 0.23/0.53    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.23/0.53    introduced(choice_axiom,[])).
% 0.23/0.53  fof(f18,plain,(
% 0.23/0.53    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.23/0.53    inference(flattening,[],[f17])).
% 0.23/0.53  fof(f17,plain,(
% 0.23/0.53    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.23/0.53    inference(ennf_transformation,[],[f16])).
% 0.23/0.53  fof(f16,negated_conjecture,(
% 0.23/0.53    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.23/0.53    inference(negated_conjecture,[],[f15])).
% 0.23/0.53  % (15845)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.23/0.53  fof(f15,conjecture,(
% 0.23/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).
% 0.23/0.53  fof(f75,plain,(
% 0.23/0.53    v1_xboole_0(k6_domain_1(sK0,sK1)) | v1_xboole_0(sK0)),
% 0.23/0.53    inference(subsumption_resolution,[],[f74,f36])).
% 0.23/0.53  fof(f36,plain,(
% 0.23/0.53    m1_subset_1(sK1,sK0)),
% 0.23/0.53    inference(cnf_transformation,[],[f30])).
% 0.23/0.53  fof(f74,plain,(
% 0.23/0.53    v1_xboole_0(k6_domain_1(sK0,sK1)) | ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0)),
% 0.23/0.53    inference(resolution,[],[f72,f48])).
% 0.23/0.53  fof(f48,plain,(
% 0.23/0.53    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f26])).
% 0.23/0.53  % (15847)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.53  fof(f26,plain,(
% 0.23/0.53    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.23/0.53    inference(flattening,[],[f25])).
% 0.23/0.53  fof(f25,plain,(
% 0.23/0.53    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.23/0.53    inference(ennf_transformation,[],[f12])).
% 0.23/0.53  fof(f12,axiom,(
% 0.23/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.23/0.53  fof(f72,plain,(
% 0.23/0.53    ~m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(k6_domain_1(sK0,sK1))),
% 0.23/0.53    inference(resolution,[],[f71,f37])).
% 0.23/0.53  fof(f37,plain,(
% 0.23/0.53    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.23/0.53    inference(cnf_transformation,[],[f30])).
% 0.23/0.53  fof(f71,plain,(
% 0.23/0.53    ( ! [X0] : (~v1_subset_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(X0)) )),
% 0.23/0.53    inference(resolution,[],[f69,f38])).
% 0.23/0.53  fof(f38,plain,(
% 0.23/0.53    v1_zfmisc_1(sK0)),
% 0.23/0.53    inference(cnf_transformation,[],[f30])).
% 0.23/0.53  fof(f69,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0)) )),
% 0.23/0.53    inference(subsumption_resolution,[],[f44,f43])).
% 0.23/0.53  fof(f43,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f20])).
% 0.23/0.53  % (15850)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.23/0.53  fof(f20,plain,(
% 0.23/0.53    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.23/0.53    inference(ennf_transformation,[],[f8])).
% 0.23/0.53  fof(f8,axiom,(
% 0.23/0.53    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).
% 0.23/0.53  fof(f44,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f22])).
% 0.23/0.53  fof(f22,plain,(
% 0.23/0.53    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.23/0.53    inference(flattening,[],[f21])).
% 0.23/0.53  fof(f21,plain,(
% 0.23/0.53    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.23/0.53    inference(ennf_transformation,[],[f14])).
% 0.23/0.53  fof(f14,axiom,(
% 0.23/0.53    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.23/0.53  fof(f89,plain,(
% 0.23/0.53    k6_domain_1(sK0,sK1) = k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.23/0.53    inference(subsumption_resolution,[],[f87,f35])).
% 0.23/0.53  fof(f87,plain,(
% 0.23/0.53    k6_domain_1(sK0,sK1) = k2_enumset1(sK1,sK1,sK1,sK1) | v1_xboole_0(sK0)),
% 0.23/0.53    inference(resolution,[],[f62,f36])).
% 0.23/0.53  fof(f62,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_enumset1(X1,X1,X1,X1) | v1_xboole_0(X0)) )),
% 0.23/0.53    inference(definition_unfolding,[],[f47,f59])).
% 0.23/0.53  fof(f59,plain,(
% 0.23/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.23/0.53    inference(definition_unfolding,[],[f40,f57])).
% 0.23/0.53  fof(f40,plain,(
% 0.23/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f4])).
% 0.23/0.53  fof(f4,axiom,(
% 0.23/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.23/0.53  fof(f47,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f24])).
% 0.23/0.53  fof(f24,plain,(
% 0.23/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.23/0.53    inference(flattening,[],[f23])).
% 0.23/0.53  fof(f23,plain,(
% 0.23/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.23/0.53    inference(ennf_transformation,[],[f13])).
% 0.23/0.53  fof(f13,axiom,(
% 0.23/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.23/0.53  fof(f68,plain,(
% 0.23/0.53    ( ! [X1] : (r2_hidden(X1,k3_tarski(k2_enumset1(X1,X1,X1,k2_enumset1(X1,X1,X1,X1))))) )),
% 0.23/0.53    inference(equality_resolution,[],[f63])).
% 0.23/0.53  fof(f63,plain,(
% 0.23/0.53    ( ! [X0,X1] : (r2_hidden(X0,k3_tarski(k2_enumset1(X1,X1,X1,k2_enumset1(X1,X1,X1,X1)))) | X0 != X1) )),
% 0.23/0.53    inference(definition_unfolding,[],[f54,f60])).
% 0.23/0.53  fof(f60,plain,(
% 0.23/0.53    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0)))) )),
% 0.23/0.53    inference(definition_unfolding,[],[f41,f58,f59])).
% 0.23/0.53  % (15843)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.23/0.53  fof(f41,plain,(
% 0.23/0.53    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f9])).
% 0.23/0.53  fof(f9,axiom,(
% 0.23/0.53    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.23/0.53  fof(f54,plain,(
% 0.23/0.53    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 0.23/0.53    inference(cnf_transformation,[],[f34])).
% 0.23/0.53  fof(f34,plain,(
% 0.23/0.53    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.23/0.53    inference(flattening,[],[f33])).
% 0.23/0.53  fof(f33,plain,(
% 0.23/0.53    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.23/0.53    inference(nnf_transformation,[],[f10])).
% 0.23/0.53  fof(f10,axiom,(
% 0.23/0.53    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.23/0.53  fof(f66,plain,(
% 0.23/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.23/0.53    inference(equality_resolution,[],[f50])).
% 0.23/0.53  fof(f50,plain,(
% 0.23/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.23/0.53    inference(cnf_transformation,[],[f32])).
% 0.23/0.53  fof(f32,plain,(
% 0.23/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.53    inference(flattening,[],[f31])).
% 0.23/0.53  fof(f31,plain,(
% 0.23/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.53    inference(nnf_transformation,[],[f2])).
% 0.23/0.53  fof(f2,axiom,(
% 0.23/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.23/0.53  % SZS output end Proof for theBenchmark
% 0.23/0.53  % (15863)------------------------------
% 0.23/0.53  % (15863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (15863)Termination reason: Refutation
% 0.23/0.53  
% 0.23/0.53  % (15863)Memory used [KB]: 6268
% 0.23/0.53  % (15863)Time elapsed: 0.056 s
% 0.23/0.53  % (15863)------------------------------
% 0.23/0.53  % (15863)------------------------------
% 0.23/0.54  % (15840)Success in time 0.163 s
%------------------------------------------------------------------------------
