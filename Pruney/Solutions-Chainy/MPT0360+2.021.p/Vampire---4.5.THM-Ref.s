%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:51 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 122 expanded)
%              Number of leaves         :   12 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  145 ( 279 expanded)
%              Number of equality atoms :   27 (  75 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f701,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f130,f132,f666,f686,f700])).

fof(f700,plain,(
    ~ spl5_35 ),
    inference(avatar_contradiction_clause,[],[f693])).

fof(f693,plain,
    ( $false
    | ~ spl5_35 ),
    inference(unit_resulting_resolution,[],[f22,f481,f665,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f665,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f663])).

fof(f663,plain,
    ( spl5_35
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f481,plain,(
    ! [X20] : r1_tarski(k1_xboole_0,X20) ),
    inference(superposition,[],[f78,f463])).

fof(f463,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(duplicate_literal_removal,[],[f446])).

fof(f446,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ) ),
    inference(resolution,[],[f90,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(k5_xboole_0(X0,k3_xboole_0(X0,X1))),X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f52,f23])).

fof(f23,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f37,f24])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f90,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(k5_xboole_0(X0,k3_xboole_0(X0,X1))),X0)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f53,f23])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f36,f24])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(resolution,[],[f41,f49])).

fof(f49,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f24])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f22,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(f686,plain,(
    spl5_34 ),
    inference(avatar_contradiction_clause,[],[f685])).

fof(f685,plain,
    ( $false
    | spl5_34 ),
    inference(subsumption_resolution,[],[f20,f661])).

fof(f661,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl5_34 ),
    inference(avatar_component_clause,[],[f659])).

fof(f659,plain,
    ( spl5_34
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f20,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f666,plain,
    ( ~ spl5_34
    | spl5_35
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f651,f127,f663,f659])).

fof(f127,plain,
    ( spl5_6
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f651,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ r1_tarski(sK1,sK2)
    | ~ spl5_6 ),
    inference(resolution,[],[f473,f129])).

fof(f129,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f127])).

fof(f473,plain,(
    ! [X6,X5] :
      ( ~ r1_xboole_0(X6,X5)
      | r1_tarski(X6,k1_xboole_0)
      | ~ r1_tarski(X6,X5) ) ),
    inference(superposition,[],[f42,f463])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f24])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f132,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | spl5_5 ),
    inference(subsumption_resolution,[],[f19,f125])).

fof(f125,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl5_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f130,plain,
    ( ~ spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f121,f127,f123])).

fof(f121,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f101,f21])).

fof(f21,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
      | r1_xboole_0(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f40,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f26,f24])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | r1_xboole_0(X0,X2) ) ),
    inference(definition_unfolding,[],[f31,f24])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:44:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.32/0.54  % (12058)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.32/0.55  % (12052)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.32/0.55  % (12079)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.32/0.55  % (12076)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.50/0.56  % (12063)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.50/0.56  % (12053)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.50/0.56  % (12068)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.50/0.56  % (12068)Refutation not found, incomplete strategy% (12068)------------------------------
% 1.50/0.56  % (12068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (12068)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (12068)Memory used [KB]: 1663
% 1.50/0.56  % (12068)Time elapsed: 0.148 s
% 1.50/0.56  % (12068)------------------------------
% 1.50/0.56  % (12068)------------------------------
% 1.50/0.56  % (12069)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.50/0.56  % (12051)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.50/0.56  % (12051)Refutation not found, incomplete strategy% (12051)------------------------------
% 1.50/0.56  % (12051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (12051)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (12051)Memory used [KB]: 1663
% 1.50/0.56  % (12051)Time elapsed: 0.152 s
% 1.50/0.56  % (12051)------------------------------
% 1.50/0.56  % (12051)------------------------------
% 1.50/0.56  % (12060)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.50/0.57  % (12060)Refutation not found, incomplete strategy% (12060)------------------------------
% 1.50/0.57  % (12060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (12076)Refutation not found, incomplete strategy% (12076)------------------------------
% 1.50/0.57  % (12076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (12076)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.57  
% 1.50/0.57  % (12076)Memory used [KB]: 6268
% 1.50/0.57  % (12076)Time elapsed: 0.148 s
% 1.50/0.57  % (12076)------------------------------
% 1.50/0.57  % (12076)------------------------------
% 1.50/0.57  % (12055)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.50/0.57  % (12079)Refutation not found, incomplete strategy% (12079)------------------------------
% 1.50/0.57  % (12079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (12079)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.57  
% 1.50/0.57  % (12079)Memory used [KB]: 1663
% 1.50/0.57  % (12079)Time elapsed: 0.141 s
% 1.50/0.57  % (12079)------------------------------
% 1.50/0.57  % (12079)------------------------------
% 1.50/0.58  % (12060)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.58  
% 1.50/0.58  % (12060)Memory used [KB]: 10746
% 1.50/0.58  % (12060)Time elapsed: 0.136 s
% 1.50/0.58  % (12060)------------------------------
% 1.50/0.58  % (12060)------------------------------
% 1.50/0.58  % (12074)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.50/0.58  % (12066)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.50/0.58  % (12066)Refutation not found, incomplete strategy% (12066)------------------------------
% 1.50/0.58  % (12066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.58  % (12066)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.58  
% 1.50/0.58  % (12066)Memory used [KB]: 10618
% 1.50/0.58  % (12066)Time elapsed: 0.178 s
% 1.50/0.58  % (12066)------------------------------
% 1.50/0.58  % (12066)------------------------------
% 1.50/0.58  % (12077)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.50/0.58  % (12077)Refutation not found, incomplete strategy% (12077)------------------------------
% 1.50/0.58  % (12077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.58  % (12077)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.58  
% 1.50/0.58  % (12077)Memory used [KB]: 6140
% 1.50/0.58  % (12077)Time elapsed: 0.161 s
% 1.50/0.58  % (12077)------------------------------
% 1.50/0.58  % (12077)------------------------------
% 1.50/0.58  % (12059)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.50/0.59  % (12057)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.50/0.59  % (12070)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.50/0.59  % (12050)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.50/0.59  % (12063)Refutation found. Thanks to Tanya!
% 1.50/0.59  % SZS status Theorem for theBenchmark
% 1.50/0.59  % SZS output start Proof for theBenchmark
% 1.50/0.59  fof(f701,plain,(
% 1.50/0.59    $false),
% 1.50/0.59    inference(avatar_sat_refutation,[],[f130,f132,f666,f686,f700])).
% 1.50/0.59  fof(f700,plain,(
% 1.50/0.59    ~spl5_35),
% 1.50/0.59    inference(avatar_contradiction_clause,[],[f693])).
% 1.50/0.59  fof(f693,plain,(
% 1.50/0.59    $false | ~spl5_35),
% 1.50/0.59    inference(unit_resulting_resolution,[],[f22,f481,f665,f29])).
% 1.50/0.59  fof(f29,plain,(
% 1.50/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.50/0.59    inference(cnf_transformation,[],[f3])).
% 1.50/0.59  fof(f3,axiom,(
% 1.50/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.50/0.59  fof(f665,plain,(
% 1.50/0.59    r1_tarski(sK1,k1_xboole_0) | ~spl5_35),
% 1.50/0.59    inference(avatar_component_clause,[],[f663])).
% 1.50/0.59  fof(f663,plain,(
% 1.50/0.59    spl5_35 <=> r1_tarski(sK1,k1_xboole_0)),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 1.50/0.59  fof(f481,plain,(
% 1.50/0.59    ( ! [X20] : (r1_tarski(k1_xboole_0,X20)) )),
% 1.50/0.59    inference(superposition,[],[f78,f463])).
% 1.50/0.59  fof(f463,plain,(
% 1.50/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 1.50/0.59    inference(duplicate_literal_removal,[],[f446])).
% 1.50/0.59  fof(f446,plain,(
% 1.50/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 1.50/0.59    inference(resolution,[],[f90,f88])).
% 1.50/0.59  fof(f88,plain,(
% 1.50/0.59    ( ! [X0,X1] : (~r2_hidden(sK3(k5_xboole_0(X0,k3_xboole_0(X0,X1))),X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.50/0.59    inference(resolution,[],[f52,f23])).
% 1.50/0.59  fof(f23,plain,(
% 1.50/0.59    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.50/0.59    inference(cnf_transformation,[],[f13])).
% 1.50/0.59  fof(f13,plain,(
% 1.50/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.50/0.59    inference(ennf_transformation,[],[f2])).
% 1.50/0.59  fof(f2,axiom,(
% 1.50/0.59    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.50/0.59  fof(f52,plain,(
% 1.50/0.59    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X3,X1)) )),
% 1.50/0.59    inference(equality_resolution,[],[f44])).
% 1.50/0.59  fof(f44,plain,(
% 1.50/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.50/0.59    inference(definition_unfolding,[],[f37,f24])).
% 1.50/0.59  fof(f24,plain,(
% 1.50/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.50/0.59    inference(cnf_transformation,[],[f4])).
% 1.50/0.60  fof(f4,axiom,(
% 1.50/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.50/0.60  fof(f37,plain,(
% 1.50/0.60    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.50/0.60    inference(cnf_transformation,[],[f1])).
% 1.50/0.60  fof(f1,axiom,(
% 1.50/0.60    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.50/0.60  fof(f90,plain,(
% 1.50/0.60    ( ! [X0,X1] : (r2_hidden(sK3(k5_xboole_0(X0,k3_xboole_0(X0,X1))),X0) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.50/0.60    inference(resolution,[],[f53,f23])).
% 1.50/0.60  fof(f53,plain,(
% 1.50/0.60    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X3,X0)) )),
% 1.50/0.60    inference(equality_resolution,[],[f45])).
% 1.50/0.60  fof(f45,plain,(
% 1.50/0.60    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.50/0.60    inference(definition_unfolding,[],[f36,f24])).
% 1.50/0.60  fof(f36,plain,(
% 1.50/0.60    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.50/0.60    inference(cnf_transformation,[],[f1])).
% 1.50/0.60  fof(f78,plain,(
% 1.50/0.60    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 1.50/0.60    inference(resolution,[],[f41,f49])).
% 1.50/0.60  fof(f49,plain,(
% 1.50/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.50/0.60    inference(equality_resolution,[],[f28])).
% 1.50/0.60  fof(f28,plain,(
% 1.50/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.50/0.60    inference(cnf_transformation,[],[f3])).
% 1.50/0.60  fof(f41,plain,(
% 1.50/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | r1_tarski(X0,X1)) )),
% 1.50/0.60    inference(definition_unfolding,[],[f30,f24])).
% 1.50/0.60  fof(f30,plain,(
% 1.50/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f16])).
% 1.50/0.60  fof(f16,plain,(
% 1.50/0.60    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.50/0.60    inference(ennf_transformation,[],[f5])).
% 1.50/0.60  fof(f5,axiom,(
% 1.50/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.50/0.60  fof(f22,plain,(
% 1.50/0.60    k1_xboole_0 != sK1),
% 1.50/0.60    inference(cnf_transformation,[],[f12])).
% 1.50/0.60  fof(f12,plain,(
% 1.50/0.60    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.50/0.60    inference(flattening,[],[f11])).
% 1.50/0.60  fof(f11,plain,(
% 1.50/0.60    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.50/0.60    inference(ennf_transformation,[],[f10])).
% 1.50/0.60  fof(f10,negated_conjecture,(
% 1.50/0.60    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.50/0.60    inference(negated_conjecture,[],[f9])).
% 1.50/0.60  fof(f9,conjecture,(
% 1.50/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).
% 1.50/0.60  fof(f686,plain,(
% 1.50/0.60    spl5_34),
% 1.50/0.60    inference(avatar_contradiction_clause,[],[f685])).
% 1.50/0.60  fof(f685,plain,(
% 1.50/0.60    $false | spl5_34),
% 1.50/0.60    inference(subsumption_resolution,[],[f20,f661])).
% 1.50/0.60  fof(f661,plain,(
% 1.50/0.60    ~r1_tarski(sK1,sK2) | spl5_34),
% 1.50/0.60    inference(avatar_component_clause,[],[f659])).
% 1.50/0.60  fof(f659,plain,(
% 1.50/0.60    spl5_34 <=> r1_tarski(sK1,sK2)),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 1.50/0.60  fof(f20,plain,(
% 1.50/0.60    r1_tarski(sK1,sK2)),
% 1.50/0.60    inference(cnf_transformation,[],[f12])).
% 1.50/0.60  fof(f666,plain,(
% 1.50/0.60    ~spl5_34 | spl5_35 | ~spl5_6),
% 1.50/0.60    inference(avatar_split_clause,[],[f651,f127,f663,f659])).
% 1.50/0.60  fof(f127,plain,(
% 1.50/0.60    spl5_6 <=> r1_xboole_0(sK1,sK2)),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.50/0.60  fof(f651,plain,(
% 1.50/0.60    r1_tarski(sK1,k1_xboole_0) | ~r1_tarski(sK1,sK2) | ~spl5_6),
% 1.50/0.60    inference(resolution,[],[f473,f129])).
% 1.50/0.60  fof(f129,plain,(
% 1.50/0.60    r1_xboole_0(sK1,sK2) | ~spl5_6),
% 1.50/0.60    inference(avatar_component_clause,[],[f127])).
% 1.50/0.60  fof(f473,plain,(
% 1.50/0.60    ( ! [X6,X5] : (~r1_xboole_0(X6,X5) | r1_tarski(X6,k1_xboole_0) | ~r1_tarski(X6,X5)) )),
% 1.50/0.60    inference(superposition,[],[f42,f463])).
% 1.50/0.60  fof(f42,plain,(
% 1.50/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.50/0.60    inference(definition_unfolding,[],[f32,f24])).
% 1.50/0.60  fof(f32,plain,(
% 1.50/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 1.50/0.60    inference(cnf_transformation,[],[f18])).
% 1.50/0.60  fof(f18,plain,(
% 1.50/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 1.50/0.60    inference(flattening,[],[f17])).
% 1.50/0.60  fof(f17,plain,(
% 1.50/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.50/0.60    inference(ennf_transformation,[],[f7])).
% 1.50/0.60  fof(f7,axiom,(
% 1.50/0.60    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).
% 1.50/0.60  fof(f132,plain,(
% 1.50/0.60    spl5_5),
% 1.50/0.60    inference(avatar_contradiction_clause,[],[f131])).
% 1.50/0.60  fof(f131,plain,(
% 1.50/0.60    $false | spl5_5),
% 1.50/0.60    inference(subsumption_resolution,[],[f19,f125])).
% 1.50/0.60  fof(f125,plain,(
% 1.50/0.60    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | spl5_5),
% 1.50/0.60    inference(avatar_component_clause,[],[f123])).
% 1.50/0.60  fof(f123,plain,(
% 1.50/0.60    spl5_5 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.50/0.60  fof(f19,plain,(
% 1.50/0.60    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.50/0.60    inference(cnf_transformation,[],[f12])).
% 1.50/0.60  fof(f130,plain,(
% 1.50/0.60    ~spl5_5 | spl5_6),
% 1.50/0.60    inference(avatar_split_clause,[],[f121,f127,f123])).
% 1.50/0.60  fof(f121,plain,(
% 1.50/0.60    r1_xboole_0(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.50/0.60    inference(resolution,[],[f101,f21])).
% 1.50/0.60  fof(f21,plain,(
% 1.50/0.60    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 1.50/0.60    inference(cnf_transformation,[],[f12])).
% 1.50/0.60  fof(f101,plain,(
% 1.50/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X2,k3_subset_1(X0,X1)) | r1_xboole_0(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.50/0.60    inference(superposition,[],[f40,f39])).
% 1.50/0.60  fof(f39,plain,(
% 1.50/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.50/0.60    inference(definition_unfolding,[],[f26,f24])).
% 1.50/0.60  fof(f26,plain,(
% 1.50/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f15])).
% 1.50/0.60  fof(f15,plain,(
% 1.50/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.50/0.60    inference(ennf_transformation,[],[f8])).
% 1.50/0.60  fof(f8,axiom,(
% 1.50/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.50/0.60  fof(f40,plain,(
% 1.50/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | r1_xboole_0(X0,X2)) )),
% 1.50/0.60    inference(definition_unfolding,[],[f31,f24])).
% 1.50/0.60  fof(f31,plain,(
% 1.50/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f16])).
% 1.50/0.60  % SZS output end Proof for theBenchmark
% 1.50/0.60  % (12063)------------------------------
% 1.50/0.60  % (12063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.60  % (12063)Termination reason: Refutation
% 1.50/0.60  
% 1.50/0.60  % (12063)Memory used [KB]: 6524
% 1.50/0.60  % (12063)Time elapsed: 0.174 s
% 1.50/0.60  % (12063)------------------------------
% 1.50/0.60  % (12063)------------------------------
% 1.50/0.60  % (12049)Success in time 0.23 s
%------------------------------------------------------------------------------
