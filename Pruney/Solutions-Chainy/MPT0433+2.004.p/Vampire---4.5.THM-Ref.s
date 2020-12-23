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
% DateTime   : Thu Dec  3 12:46:52 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 112 expanded)
%              Number of leaves         :   18 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :  158 ( 290 expanded)
%              Number of equality atoms :   18 (  32 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f396,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f62,f96,f354,f395])).

fof(f395,plain,
    ( ~ spl2_2
    | spl2_5 ),
    inference(avatar_contradiction_clause,[],[f393])).

fof(f393,plain,
    ( $false
    | ~ spl2_2
    | spl2_5 ),
    inference(unit_resulting_resolution,[],[f56,f110,f46,f95,f140])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X2)
      | r1_tarski(k1_relat_1(X0),X2)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f138,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f42,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X2)
      | r1_tarski(k1_relat_1(X0),X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f101,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f101,plain,(
    ! [X8,X7,X9] :
      ( ~ r1_tarski(k1_relat_1(k2_xboole_0(X7,X8)),X9)
      | r1_tarski(k1_relat_1(X7),X9)
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(X7) ) ),
    inference(superposition,[],[f32,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f95,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl2_5
  <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f46,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f110,plain,(
    ! [X6,X5] : r1_tarski(k3_xboole_0(X6,X5),X5) ),
    inference(superposition,[],[f39,f106])).

fof(f106,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f68,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f41,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f56,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f354,plain,
    ( ~ spl2_3
    | spl2_4 ),
    inference(avatar_contradiction_clause,[],[f339])).

fof(f339,plain,
    ( $false
    | ~ spl2_3
    | spl2_4 ),
    inference(unit_resulting_resolution,[],[f61,f39,f91,f46,f140])).

fof(f91,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl2_4
  <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f61,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl2_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f96,plain,
    ( ~ spl2_4
    | ~ spl2_5
    | spl2_1 ),
    inference(avatar_split_clause,[],[f84,f49,f93,f89])).

fof(f49,plain,
    ( spl2_1
  <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f84,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))
    | spl2_1 ),
    inference(resolution,[],[f31,f51])).

fof(f51,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f62,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f28,f59])).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).

fof(f57,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f29,f54])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f30,f49])).

fof(f30,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:38:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.53  % (13988)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (13972)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (13976)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.31/0.54  % (13980)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.31/0.54  % (13968)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.31/0.55  % (13969)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.46/0.56  % (13976)Refutation not found, incomplete strategy% (13976)------------------------------
% 1.46/0.56  % (13976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (13976)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.56  
% 1.46/0.56  % (13976)Memory used [KB]: 10746
% 1.46/0.56  % (13976)Time elapsed: 0.144 s
% 1.46/0.56  % (13976)------------------------------
% 1.46/0.56  % (13976)------------------------------
% 1.46/0.57  % (13973)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.46/0.57  % (13992)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.46/0.58  % (13987)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.46/0.58  % (13981)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.46/0.58  % (13967)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.46/0.58  % (13978)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.46/0.58  % (13975)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.46/0.58  % (13995)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.46/0.58  % (13989)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.46/0.58  % (13986)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.46/0.58  % (13984)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.46/0.59  % (13970)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.46/0.59  % (13979)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.46/0.59  % (13966)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.46/0.59  % (13994)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.46/0.59  % (13971)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.46/0.60  % (13974)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.46/0.60  % (13985)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.46/0.60  % (13977)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.46/0.60  % (13993)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.46/0.61  % (13990)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.46/0.61  % (13987)Refutation found. Thanks to Tanya!
% 1.46/0.61  % SZS status Theorem for theBenchmark
% 1.46/0.61  % SZS output start Proof for theBenchmark
% 1.46/0.61  fof(f396,plain,(
% 1.46/0.61    $false),
% 1.46/0.61    inference(avatar_sat_refutation,[],[f52,f57,f62,f96,f354,f395])).
% 1.46/0.61  fof(f395,plain,(
% 1.46/0.61    ~spl2_2 | spl2_5),
% 1.46/0.61    inference(avatar_contradiction_clause,[],[f393])).
% 1.46/0.61  fof(f393,plain,(
% 1.46/0.61    $false | (~spl2_2 | spl2_5)),
% 1.46/0.61    inference(unit_resulting_resolution,[],[f56,f110,f46,f95,f140])).
% 1.46/0.61  fof(f140,plain,(
% 1.46/0.61    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X1),X2) | r1_tarski(k1_relat_1(X0),X2) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1)) )),
% 1.46/0.61    inference(subsumption_resolution,[],[f138,f73])).
% 1.46/0.61  fof(f73,plain,(
% 1.46/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) )),
% 1.46/0.61    inference(resolution,[],[f42,f34])).
% 1.46/0.61  fof(f34,plain,(
% 1.46/0.61    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.46/0.61    inference(cnf_transformation,[],[f25])).
% 1.46/0.61  fof(f25,plain,(
% 1.46/0.61    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.46/0.61    inference(nnf_transformation,[],[f10])).
% 1.46/0.61  fof(f10,axiom,(
% 1.46/0.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.46/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.46/0.61  fof(f42,plain,(
% 1.46/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.46/0.61    inference(cnf_transformation,[],[f21])).
% 1.46/0.61  fof(f21,plain,(
% 1.46/0.61    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.46/0.61    inference(ennf_transformation,[],[f11])).
% 1.46/0.61  fof(f11,axiom,(
% 1.46/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.46/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.46/0.61  fof(f138,plain,(
% 1.46/0.61    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X1),X2) | r1_tarski(k1_relat_1(X0),X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | ~r1_tarski(X0,X1)) )),
% 1.46/0.61    inference(superposition,[],[f101,f38])).
% 1.46/0.61  fof(f38,plain,(
% 1.46/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.46/0.61    inference(cnf_transformation,[],[f19])).
% 1.46/0.61  fof(f19,plain,(
% 1.46/0.61    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.46/0.61    inference(ennf_transformation,[],[f3])).
% 1.46/0.61  fof(f3,axiom,(
% 1.46/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.46/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.46/0.61  fof(f101,plain,(
% 1.46/0.61    ( ! [X8,X7,X9] : (~r1_tarski(k1_relat_1(k2_xboole_0(X7,X8)),X9) | r1_tarski(k1_relat_1(X7),X9) | ~v1_relat_1(X8) | ~v1_relat_1(X7)) )),
% 1.46/0.61    inference(superposition,[],[f32,f40])).
% 1.46/0.61  fof(f40,plain,(
% 1.46/0.61    ( ! [X0,X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.46/0.61    inference(cnf_transformation,[],[f20])).
% 1.46/0.61  fof(f20,plain,(
% 1.46/0.61    ! [X0] : (! [X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.46/0.61    inference(ennf_transformation,[],[f12])).
% 1.46/0.61  fof(f12,axiom,(
% 1.46/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))))),
% 1.46/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).
% 1.46/0.61  fof(f32,plain,(
% 1.46/0.61    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.46/0.61    inference(cnf_transformation,[],[f18])).
% 1.46/0.61  fof(f18,plain,(
% 1.46/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.46/0.61    inference(ennf_transformation,[],[f2])).
% 1.46/0.61  fof(f2,axiom,(
% 1.46/0.61    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.46/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.46/0.61  fof(f95,plain,(
% 1.46/0.61    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) | spl2_5),
% 1.46/0.61    inference(avatar_component_clause,[],[f93])).
% 1.46/0.61  fof(f93,plain,(
% 1.46/0.61    spl2_5 <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1))),
% 1.46/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.46/0.61  fof(f46,plain,(
% 1.46/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.46/0.61    inference(equality_resolution,[],[f36])).
% 1.46/0.61  fof(f36,plain,(
% 1.46/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.46/0.61    inference(cnf_transformation,[],[f27])).
% 1.46/0.61  fof(f27,plain,(
% 1.46/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.46/0.61    inference(flattening,[],[f26])).
% 1.46/0.61  fof(f26,plain,(
% 1.46/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.46/0.61    inference(nnf_transformation,[],[f1])).
% 1.46/0.61  fof(f1,axiom,(
% 1.46/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.46/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.46/0.61  fof(f110,plain,(
% 1.46/0.61    ( ! [X6,X5] : (r1_tarski(k3_xboole_0(X6,X5),X5)) )),
% 1.46/0.61    inference(superposition,[],[f39,f106])).
% 1.46/0.61  fof(f106,plain,(
% 1.46/0.61    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 1.46/0.61    inference(superposition,[],[f68,f41])).
% 1.46/0.61  fof(f41,plain,(
% 1.46/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.46/0.61    inference(cnf_transformation,[],[f9])).
% 1.46/0.61  fof(f9,axiom,(
% 1.46/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.46/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.46/0.61  fof(f68,plain,(
% 1.46/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 1.46/0.61    inference(superposition,[],[f41,f44])).
% 1.46/0.61  fof(f44,plain,(
% 1.46/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.46/0.61    inference(cnf_transformation,[],[f6])).
% 1.46/0.61  fof(f6,axiom,(
% 1.46/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.46/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.46/0.61  fof(f39,plain,(
% 1.46/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.46/0.61    inference(cnf_transformation,[],[f4])).
% 1.46/0.61  fof(f4,axiom,(
% 1.46/0.61    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.46/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.46/0.61  fof(f56,plain,(
% 1.46/0.61    v1_relat_1(sK1) | ~spl2_2),
% 1.46/0.61    inference(avatar_component_clause,[],[f54])).
% 1.46/0.61  fof(f54,plain,(
% 1.46/0.61    spl2_2 <=> v1_relat_1(sK1)),
% 1.46/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.46/0.61  fof(f354,plain,(
% 1.46/0.61    ~spl2_3 | spl2_4),
% 1.46/0.61    inference(avatar_contradiction_clause,[],[f339])).
% 1.46/0.61  fof(f339,plain,(
% 1.46/0.61    $false | (~spl2_3 | spl2_4)),
% 1.46/0.61    inference(unit_resulting_resolution,[],[f61,f39,f91,f46,f140])).
% 1.46/0.61  fof(f91,plain,(
% 1.46/0.61    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) | spl2_4),
% 1.46/0.61    inference(avatar_component_clause,[],[f89])).
% 1.46/0.61  fof(f89,plain,(
% 1.46/0.61    spl2_4 <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))),
% 1.46/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.46/0.61  fof(f61,plain,(
% 1.46/0.61    v1_relat_1(sK0) | ~spl2_3),
% 1.46/0.61    inference(avatar_component_clause,[],[f59])).
% 1.46/0.61  fof(f59,plain,(
% 1.46/0.61    spl2_3 <=> v1_relat_1(sK0)),
% 1.46/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.46/0.61  fof(f96,plain,(
% 1.46/0.61    ~spl2_4 | ~spl2_5 | spl2_1),
% 1.46/0.61    inference(avatar_split_clause,[],[f84,f49,f93,f89])).
% 1.46/0.61  fof(f49,plain,(
% 1.46/0.61    spl2_1 <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),
% 1.46/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.46/0.61  fof(f84,plain,(
% 1.46/0.61    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) | spl2_1),
% 1.46/0.61    inference(resolution,[],[f31,f51])).
% 1.46/0.61  fof(f51,plain,(
% 1.46/0.61    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) | spl2_1),
% 1.46/0.61    inference(avatar_component_clause,[],[f49])).
% 1.46/0.61  fof(f31,plain,(
% 1.46/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.46/0.61    inference(cnf_transformation,[],[f17])).
% 1.46/0.61  fof(f17,plain,(
% 1.46/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.46/0.61    inference(flattening,[],[f16])).
% 1.46/0.61  fof(f16,plain,(
% 1.46/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.46/0.61    inference(ennf_transformation,[],[f5])).
% 1.46/0.61  fof(f5,axiom,(
% 1.46/0.61    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.46/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.46/0.61  fof(f62,plain,(
% 1.46/0.61    spl2_3),
% 1.46/0.61    inference(avatar_split_clause,[],[f28,f59])).
% 1.46/0.61  fof(f28,plain,(
% 1.46/0.61    v1_relat_1(sK0)),
% 1.46/0.61    inference(cnf_transformation,[],[f24])).
% 1.46/0.61  fof(f24,plain,(
% 1.46/0.61    (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 1.46/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f23,f22])).
% 1.46/0.61  fof(f22,plain,(
% 1.46/0.61    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 1.46/0.61    introduced(choice_axiom,[])).
% 1.46/0.61  fof(f23,plain,(
% 1.46/0.61    ? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) & v1_relat_1(sK1))),
% 1.46/0.61    introduced(choice_axiom,[])).
% 1.46/0.61  fof(f15,plain,(
% 1.46/0.61    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.46/0.61    inference(ennf_transformation,[],[f14])).
% 1.46/0.61  fof(f14,negated_conjecture,(
% 1.46/0.61    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 1.46/0.61    inference(negated_conjecture,[],[f13])).
% 1.46/0.61  fof(f13,conjecture,(
% 1.46/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 1.46/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).
% 1.46/0.61  fof(f57,plain,(
% 1.46/0.61    spl2_2),
% 1.46/0.61    inference(avatar_split_clause,[],[f29,f54])).
% 1.46/0.61  fof(f29,plain,(
% 1.46/0.61    v1_relat_1(sK1)),
% 1.46/0.61    inference(cnf_transformation,[],[f24])).
% 1.46/0.61  fof(f52,plain,(
% 1.46/0.61    ~spl2_1),
% 1.46/0.61    inference(avatar_split_clause,[],[f30,f49])).
% 1.46/0.61  fof(f30,plain,(
% 1.46/0.61    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),
% 1.46/0.61    inference(cnf_transformation,[],[f24])).
% 1.46/0.61  % SZS output end Proof for theBenchmark
% 1.46/0.61  % (13987)------------------------------
% 1.46/0.61  % (13987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.61  % (13987)Termination reason: Refutation
% 1.46/0.61  
% 1.46/0.61  % (13987)Memory used [KB]: 6524
% 1.46/0.61  % (13987)Time elapsed: 0.201 s
% 1.46/0.61  % (13987)------------------------------
% 1.46/0.61  % (13987)------------------------------
% 1.46/0.61  % (13994)Refutation not found, incomplete strategy% (13994)------------------------------
% 1.46/0.61  % (13994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.61  % (13994)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.61  
% 1.46/0.61  % (13994)Memory used [KB]: 10618
% 1.46/0.61  % (13994)Time elapsed: 0.166 s
% 1.46/0.61  % (13994)------------------------------
% 1.46/0.61  % (13994)------------------------------
% 1.46/0.62  % (13982)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.46/0.62  % (13982)Refutation not found, incomplete strategy% (13982)------------------------------
% 1.46/0.62  % (13982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.62  % (13982)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.62  
% 1.46/0.62  % (13982)Memory used [KB]: 10618
% 1.46/0.62  % (13982)Time elapsed: 0.204 s
% 1.46/0.62  % (13982)------------------------------
% 1.46/0.62  % (13982)------------------------------
% 1.46/0.62  % (13983)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.46/0.63  % (13965)Success in time 0.264 s
%------------------------------------------------------------------------------
