%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:17 EST 2020

% Result     : Theorem 1.67s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 121 expanded)
%              Number of leaves         :   14 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :  145 ( 283 expanded)
%              Number of equality atoms :   14 (  44 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f89,f113])).

fof(f113,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl2_2 ),
    inference(subsumption_resolution,[],[f111,f26])).

fof(f26,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

fof(f111,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_2 ),
    inference(subsumption_resolution,[],[f110,f57])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X0)),X0) ),
    inference(superposition,[],[f51,f42])).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f30,f31,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(resolution,[],[f43,f45])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f31])).

fof(f32,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f110,plain,
    ( ~ r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK1)
    | ~ v1_relat_1(sK1)
    | spl2_2 ),
    inference(resolution,[],[f84,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f28,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f29,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(f84,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl2_2
  <=> r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f89,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f87,f25])).

fof(f25,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f87,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_1 ),
    inference(subsumption_resolution,[],[f86,f51])).

fof(f86,plain,
    ( ~ r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK0)
    | ~ v1_relat_1(sK0)
    | spl2_1 ),
    inference(resolution,[],[f80,f68])).

fof(f80,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl2_1
  <=> r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f85,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f74,f82,f78])).

fof(f74,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK1))
    | ~ r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK0)) ),
    inference(resolution,[],[f44,f41])).

fof(f41,plain,(
    ~ r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f27,f40,f40])).

fof(f27,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:03:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.55  % (30784)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.57  % (30793)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (30771)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.57  % (30785)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.57  % (30776)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.57  % (30770)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.57  % (30767)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.57  % (30773)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.57  % (30792)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.57  % (30775)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.58  % (30777)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.58  % (30793)Refutation not found, incomplete strategy% (30793)------------------------------
% 0.21/0.58  % (30793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (30777)Refutation not found, incomplete strategy% (30777)------------------------------
% 0.21/0.58  % (30777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (30793)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (30793)Memory used [KB]: 6140
% 0.21/0.58  % (30793)Time elapsed: 0.142 s
% 0.21/0.58  % (30793)------------------------------
% 0.21/0.58  % (30793)------------------------------
% 0.21/0.58  % (30772)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.67/0.58  % (30768)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.67/0.58  % (30777)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.58  
% 1.67/0.58  % (30777)Memory used [KB]: 10618
% 1.67/0.58  % (30777)Time elapsed: 0.141 s
% 1.67/0.58  % (30777)------------------------------
% 1.67/0.58  % (30777)------------------------------
% 1.67/0.58  % (30768)Refutation not found, incomplete strategy% (30768)------------------------------
% 1.67/0.58  % (30768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.58  % (30768)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.58  
% 1.67/0.58  % (30768)Memory used [KB]: 1663
% 1.67/0.58  % (30768)Time elapsed: 0.113 s
% 1.67/0.58  % (30768)------------------------------
% 1.67/0.58  % (30768)------------------------------
% 1.67/0.58  % (30790)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.67/0.59  % (30769)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.67/0.59  % (30774)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.67/0.60  % (30773)Refutation found. Thanks to Tanya!
% 1.67/0.60  % SZS status Theorem for theBenchmark
% 1.67/0.60  % SZS output start Proof for theBenchmark
% 1.67/0.60  fof(f114,plain,(
% 1.67/0.60    $false),
% 1.67/0.60    inference(avatar_sat_refutation,[],[f85,f89,f113])).
% 1.67/0.60  fof(f113,plain,(
% 1.67/0.60    spl2_2),
% 1.67/0.60    inference(avatar_contradiction_clause,[],[f112])).
% 1.67/0.60  fof(f112,plain,(
% 1.67/0.60    $false | spl2_2),
% 1.67/0.60    inference(subsumption_resolution,[],[f111,f26])).
% 1.67/0.60  fof(f26,plain,(
% 1.67/0.60    v1_relat_1(sK1)),
% 1.67/0.60    inference(cnf_transformation,[],[f21])).
% 1.67/0.60  fof(f21,plain,(
% 1.67/0.60    (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 1.67/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f20,f19])).
% 1.67/0.60  fof(f19,plain,(
% 1.67/0.60    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 1.67/0.60    introduced(choice_axiom,[])).
% 1.67/0.60  fof(f20,plain,(
% 1.67/0.60    ? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1))),
% 1.67/0.60    introduced(choice_axiom,[])).
% 1.67/0.60  fof(f12,plain,(
% 1.67/0.60    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.67/0.60    inference(ennf_transformation,[],[f11])).
% 1.67/0.60  fof(f11,negated_conjecture,(
% 1.67/0.60    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.67/0.60    inference(negated_conjecture,[],[f10])).
% 1.67/0.60  fof(f10,conjecture,(
% 1.67/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).
% 1.67/0.60  fof(f111,plain,(
% 1.67/0.60    ~v1_relat_1(sK1) | spl2_2),
% 1.67/0.60    inference(subsumption_resolution,[],[f110,f57])).
% 1.67/0.60  fof(f57,plain,(
% 1.67/0.60    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X0)),X0)) )),
% 1.67/0.60    inference(superposition,[],[f51,f42])).
% 1.67/0.60  fof(f42,plain,(
% 1.67/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 1.67/0.60    inference(definition_unfolding,[],[f30,f31,f31])).
% 1.67/0.60  fof(f31,plain,(
% 1.67/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f5])).
% 1.67/0.60  fof(f5,axiom,(
% 1.67/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.67/0.60  fof(f30,plain,(
% 1.67/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f4])).
% 1.67/0.60  fof(f4,axiom,(
% 1.67/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.67/0.60  fof(f51,plain,(
% 1.67/0.60    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 1.67/0.60    inference(resolution,[],[f43,f45])).
% 1.67/0.60  fof(f45,plain,(
% 1.67/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.67/0.60    inference(equality_resolution,[],[f34])).
% 1.67/0.60  fof(f34,plain,(
% 1.67/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.67/0.60    inference(cnf_transformation,[],[f23])).
% 1.67/0.60  fof(f23,plain,(
% 1.67/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.67/0.60    inference(flattening,[],[f22])).
% 1.67/0.60  fof(f22,plain,(
% 1.67/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.67/0.60    inference(nnf_transformation,[],[f1])).
% 1.67/0.60  fof(f1,axiom,(
% 1.67/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.67/0.60  fof(f43,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) | r1_tarski(X0,X1)) )),
% 1.67/0.60    inference(definition_unfolding,[],[f38,f40])).
% 1.67/0.60  fof(f40,plain,(
% 1.67/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.67/0.60    inference(definition_unfolding,[],[f32,f31])).
% 1.67/0.60  fof(f32,plain,(
% 1.67/0.60    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f6])).
% 1.67/0.60  fof(f6,axiom,(
% 1.67/0.60    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.67/0.60  fof(f38,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 1.67/0.60    inference(cnf_transformation,[],[f16])).
% 1.67/0.60  fof(f16,plain,(
% 1.67/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.67/0.60    inference(ennf_transformation,[],[f2])).
% 1.67/0.60  fof(f2,axiom,(
% 1.67/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).
% 1.67/0.60  fof(f110,plain,(
% 1.67/0.60    ~r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK1) | ~v1_relat_1(sK1) | spl2_2),
% 1.67/0.60    inference(resolution,[],[f84,f68])).
% 1.67/0.60  fof(f68,plain,(
% 1.67/0.60    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) )),
% 1.67/0.60    inference(subsumption_resolution,[],[f28,f48])).
% 1.67/0.60  fof(f48,plain,(
% 1.67/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) )),
% 1.67/0.60    inference(resolution,[],[f29,f37])).
% 1.67/0.60  fof(f37,plain,(
% 1.67/0.60    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f24])).
% 1.67/0.60  fof(f24,plain,(
% 1.67/0.60    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.67/0.60    inference(nnf_transformation,[],[f7])).
% 1.67/0.60  fof(f7,axiom,(
% 1.67/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.67/0.60  fof(f29,plain,(
% 1.67/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f15])).
% 1.67/0.60  fof(f15,plain,(
% 1.67/0.60    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.67/0.60    inference(ennf_transformation,[],[f8])).
% 1.67/0.60  fof(f8,axiom,(
% 1.67/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.67/0.60  fof(f28,plain,(
% 1.67/0.60    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f14])).
% 1.67/0.60  fof(f14,plain,(
% 1.67/0.60    ! [X0] : (! [X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.67/0.60    inference(flattening,[],[f13])).
% 1.67/0.60  fof(f13,plain,(
% 1.67/0.60    ! [X0] : (! [X1] : ((r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.67/0.60    inference(ennf_transformation,[],[f9])).
% 1.67/0.60  fof(f9,axiom,(
% 1.67/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).
% 1.67/0.60  fof(f84,plain,(
% 1.67/0.60    ~r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK1)) | spl2_2),
% 1.67/0.60    inference(avatar_component_clause,[],[f82])).
% 1.67/0.60  fof(f82,plain,(
% 1.67/0.60    spl2_2 <=> r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK1))),
% 1.67/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.67/0.60  fof(f89,plain,(
% 1.67/0.60    spl2_1),
% 1.67/0.60    inference(avatar_contradiction_clause,[],[f88])).
% 1.67/0.60  fof(f88,plain,(
% 1.67/0.60    $false | spl2_1),
% 1.67/0.60    inference(subsumption_resolution,[],[f87,f25])).
% 1.67/0.60  fof(f25,plain,(
% 1.67/0.60    v1_relat_1(sK0)),
% 1.67/0.60    inference(cnf_transformation,[],[f21])).
% 1.67/0.60  fof(f87,plain,(
% 1.67/0.60    ~v1_relat_1(sK0) | spl2_1),
% 1.67/0.60    inference(subsumption_resolution,[],[f86,f51])).
% 1.67/0.60  fof(f86,plain,(
% 1.67/0.60    ~r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK0) | ~v1_relat_1(sK0) | spl2_1),
% 1.67/0.60    inference(resolution,[],[f80,f68])).
% 1.67/0.60  fof(f80,plain,(
% 1.67/0.60    ~r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK0)) | spl2_1),
% 1.67/0.60    inference(avatar_component_clause,[],[f78])).
% 1.67/0.60  fof(f78,plain,(
% 1.67/0.60    spl2_1 <=> r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK0))),
% 1.67/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.67/0.60  fof(f85,plain,(
% 1.67/0.60    ~spl2_1 | ~spl2_2),
% 1.67/0.60    inference(avatar_split_clause,[],[f74,f82,f78])).
% 1.67/0.60  fof(f74,plain,(
% 1.67/0.60    ~r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK1)) | ~r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK0))),
% 1.67/0.60    inference(resolution,[],[f44,f41])).
% 1.67/0.60  fof(f41,plain,(
% 1.67/0.60    ~r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK1))))),
% 1.67/0.60    inference(definition_unfolding,[],[f27,f40,f40])).
% 1.67/0.60  fof(f27,plain,(
% 1.67/0.60    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))),
% 1.67/0.60    inference(cnf_transformation,[],[f21])).
% 1.67/0.60  fof(f44,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.67/0.60    inference(definition_unfolding,[],[f39,f40])).
% 1.67/0.60  fof(f39,plain,(
% 1.67/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.67/0.60    inference(cnf_transformation,[],[f18])).
% 1.67/0.60  fof(f18,plain,(
% 1.67/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.67/0.60    inference(flattening,[],[f17])).
% 1.67/0.60  fof(f17,plain,(
% 1.67/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.67/0.60    inference(ennf_transformation,[],[f3])).
% 1.67/0.60  fof(f3,axiom,(
% 1.67/0.60    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.67/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.67/0.60  % SZS output end Proof for theBenchmark
% 1.67/0.60  % (30773)------------------------------
% 1.67/0.60  % (30773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.60  % (30773)Termination reason: Refutation
% 1.67/0.60  
% 1.67/0.60  % (30773)Memory used [KB]: 10746
% 1.67/0.60  % (30773)Time elapsed: 0.147 s
% 1.67/0.60  % (30773)------------------------------
% 1.67/0.60  % (30773)------------------------------
% 1.67/0.60  % (30782)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.67/0.60  % (30766)Success in time 0.234 s
%------------------------------------------------------------------------------
