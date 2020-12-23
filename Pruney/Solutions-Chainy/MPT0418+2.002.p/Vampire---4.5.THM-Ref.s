%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:26 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 107 expanded)
%              Number of leaves         :    9 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  115 ( 281 expanded)
%              Number of equality atoms :   15 (  28 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f101,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f84,f90,f100])).

fof(f100,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f76,f93])).

fof(f93,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f91,f36])).

fof(f36,plain,(
    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f19,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <~> r2_hidden(X2,X1) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
            <=> r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_setfam_1)).

fof(f91,plain,
    ( r2_hidden(k3_subset_1(sK0,k3_subset_1(sK0,sK2)),sK1)
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f20,f50,f40,f73,f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | r2_hidden(k3_subset_1(X0,X3),X1)
      | ~ r2_hidden(X3,k7_setfam_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | r2_hidden(k3_subset_1(X0,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k7_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

fof(f73,plain,
    ( r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl4_1
  <=> r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f40,plain,(
    m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f20,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f50,plain,(
    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f31,f35])).

fof(f35,plain,(
    k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f19,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f31,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f76,plain,
    ( ~ r2_hidden(sK2,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl4_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f90,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f87])).

fof(f87,plain,
    ( $false
    | spl4_1
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f77,f86])).

fof(f86,plain,
    ( ~ r2_hidden(sK2,sK1)
    | spl4_1 ),
    inference(forward_demodulation,[],[f85,f36])).

fof(f85,plain,
    ( ~ r2_hidden(k3_subset_1(sK0,k3_subset_1(sK0,sK2)),sK1)
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f20,f50,f40,f72,f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ r2_hidden(k3_subset_1(X0,X3),X1)
      | r2_hidden(X3,k7_setfam_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

% (9308)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (9295)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (9284)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% (9299)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (9300)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (9282)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% (9299)Refutation not found, incomplete strategy% (9299)------------------------------
% (9299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9299)Termination reason: Refutation not found, incomplete strategy

% (9311)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (9299)Memory used [KB]: 10618
% (9299)Time elapsed: 0.117 s
% (9299)------------------------------
% (9299)------------------------------
% (9297)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (9291)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (9287)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (9301)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (9292)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (9310)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (9309)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (9303)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (9283)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (9289)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ r2_hidden(k3_subset_1(X0,X3),X1)
      | r2_hidden(X3,X2)
      | k7_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f72,plain,
    ( ~ r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f77,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f84,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f18,f75,f71])).

fof(f18,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f78,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f17,f75,f71])).

fof(f17,plain,
    ( r2_hidden(sK2,sK1)
    | r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:51:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.55  % (9298)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (9306)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (9288)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.55  % (9290)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.47/0.56  % (9296)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.47/0.57  % (9304)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.47/0.57  % (9286)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.47/0.57  % (9304)Refutation not found, incomplete strategy% (9304)------------------------------
% 1.47/0.57  % (9304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (9304)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.57  
% 1.47/0.57  % (9304)Memory used [KB]: 10746
% 1.47/0.57  % (9304)Time elapsed: 0.145 s
% 1.47/0.57  % (9304)------------------------------
% 1.47/0.57  % (9304)------------------------------
% 1.47/0.57  % (9286)Refutation found. Thanks to Tanya!
% 1.47/0.57  % SZS status Theorem for theBenchmark
% 1.47/0.57  % SZS output start Proof for theBenchmark
% 1.47/0.57  fof(f101,plain,(
% 1.47/0.57    $false),
% 1.47/0.57    inference(avatar_sat_refutation,[],[f78,f84,f90,f100])).
% 1.47/0.57  fof(f100,plain,(
% 1.47/0.57    ~spl4_1 | spl4_2),
% 1.47/0.57    inference(avatar_contradiction_clause,[],[f94])).
% 1.47/0.57  fof(f94,plain,(
% 1.47/0.57    $false | (~spl4_1 | spl4_2)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f76,f93])).
% 1.47/0.57  fof(f93,plain,(
% 1.47/0.57    r2_hidden(sK2,sK1) | ~spl4_1),
% 1.47/0.57    inference(forward_demodulation,[],[f91,f36])).
% 1.47/0.57  fof(f36,plain,(
% 1.47/0.57    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f19,f28])).
% 1.47/0.57  fof(f28,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.47/0.57    inference(cnf_transformation,[],[f15])).
% 1.47/0.57  fof(f15,plain,(
% 1.47/0.57    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.47/0.57    inference(ennf_transformation,[],[f3])).
% 1.47/0.57  fof(f3,axiom,(
% 1.47/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.47/0.57  fof(f19,plain,(
% 1.47/0.57    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.47/0.57    inference(cnf_transformation,[],[f10])).
% 1.47/0.57  fof(f10,plain,(
% 1.47/0.57    ? [X0,X1] : (? [X2] : ((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <~> r2_hidden(X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.47/0.57    inference(ennf_transformation,[],[f9])).
% 1.47/0.57  fof(f9,negated_conjecture,(
% 1.47/0.57    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1))))),
% 1.47/0.57    inference(negated_conjecture,[],[f8])).
% 1.47/0.57  fof(f8,conjecture,(
% 1.47/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1))))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_setfam_1)).
% 1.47/0.57  fof(f91,plain,(
% 1.47/0.57    r2_hidden(k3_subset_1(sK0,k3_subset_1(sK0,sK2)),sK1) | ~spl4_1),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f20,f50,f40,f73,f33])).
% 1.47/0.57  fof(f33,plain,(
% 1.47/0.57    ( ! [X0,X3,X1] : (~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,k7_setfam_1(X0,X1))) )),
% 1.47/0.57    inference(equality_resolution,[],[f25])).
% 1.47/0.57  fof(f25,plain,(
% 1.47/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2) | k7_setfam_1(X0,X1) != X2) )),
% 1.47/0.57    inference(cnf_transformation,[],[f13])).
% 1.47/0.57  fof(f13,plain,(
% 1.47/0.57    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.47/0.57    inference(ennf_transformation,[],[f5])).
% 1.47/0.57  fof(f5,axiom,(
% 1.47/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).
% 1.47/0.57  fof(f73,plain,(
% 1.47/0.57    r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1)) | ~spl4_1),
% 1.47/0.57    inference(avatar_component_clause,[],[f71])).
% 1.47/0.57  fof(f71,plain,(
% 1.47/0.57    spl4_1 <=> r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.47/0.57  fof(f40,plain,(
% 1.47/0.57    m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f20,f27])).
% 1.47/0.57  fof(f27,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.47/0.57    inference(cnf_transformation,[],[f14])).
% 1.47/0.57  fof(f14,plain,(
% 1.47/0.57    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.47/0.57    inference(ennf_transformation,[],[f6])).
% 1.47/0.57  fof(f6,axiom,(
% 1.47/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 1.47/0.57  fof(f50,plain,(
% 1.47/0.57    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 1.47/0.57    inference(superposition,[],[f31,f35])).
% 1.47/0.57  fof(f35,plain,(
% 1.47/0.57    k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f19,f32])).
% 1.47/0.57  fof(f32,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.47/0.57    inference(definition_unfolding,[],[f29,f30])).
% 1.47/0.57  fof(f30,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f4])).
% 1.47/0.57  fof(f4,axiom,(
% 1.47/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.47/0.57  fof(f29,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f16])).
% 1.47/0.57  fof(f16,plain,(
% 1.47/0.57    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.47/0.57    inference(ennf_transformation,[],[f1])).
% 1.47/0.57  fof(f1,axiom,(
% 1.47/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.47/0.57  fof(f31,plain,(
% 1.47/0.57    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.47/0.57    inference(cnf_transformation,[],[f2])).
% 1.47/0.57  fof(f2,axiom,(
% 1.47/0.57    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 1.47/0.57  fof(f20,plain,(
% 1.47/0.57    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.47/0.57    inference(cnf_transformation,[],[f10])).
% 1.47/0.57  fof(f76,plain,(
% 1.47/0.57    ~r2_hidden(sK2,sK1) | spl4_2),
% 1.47/0.57    inference(avatar_component_clause,[],[f75])).
% 1.47/0.57  fof(f75,plain,(
% 1.47/0.57    spl4_2 <=> r2_hidden(sK2,sK1)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.47/0.57  fof(f90,plain,(
% 1.47/0.57    spl4_1 | ~spl4_2),
% 1.47/0.57    inference(avatar_contradiction_clause,[],[f87])).
% 1.47/0.57  fof(f87,plain,(
% 1.47/0.57    $false | (spl4_1 | ~spl4_2)),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f77,f86])).
% 1.47/0.57  fof(f86,plain,(
% 1.47/0.57    ~r2_hidden(sK2,sK1) | spl4_1),
% 1.47/0.57    inference(forward_demodulation,[],[f85,f36])).
% 1.47/0.57  fof(f85,plain,(
% 1.47/0.57    ~r2_hidden(k3_subset_1(sK0,k3_subset_1(sK0,sK2)),sK1) | spl4_1),
% 1.47/0.57    inference(unit_resulting_resolution,[],[f20,f50,f40,f72,f34])).
% 1.47/0.57  fof(f34,plain,(
% 1.47/0.57    ( ! [X0,X3,X1] : (~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,k7_setfam_1(X0,X1))) )),
% 1.47/0.57    inference(equality_resolution,[],[f24])).
% 1.47/0.58  % (9308)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.61/0.58  % (9295)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.61/0.58  % (9284)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.61/0.58  % (9299)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.61/0.58  % (9300)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.61/0.58  % (9282)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.61/0.58  % (9299)Refutation not found, incomplete strategy% (9299)------------------------------
% 1.61/0.58  % (9299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.58  % (9299)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.58  
% 1.61/0.58  % (9311)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.61/0.58  % (9299)Memory used [KB]: 10618
% 1.61/0.58  % (9299)Time elapsed: 0.117 s
% 1.61/0.58  % (9299)------------------------------
% 1.61/0.58  % (9299)------------------------------
% 1.61/0.58  % (9297)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.61/0.58  % (9291)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.61/0.59  % (9287)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.61/0.59  % (9301)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.61/0.59  % (9292)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.61/0.59  % (9310)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.61/0.59  % (9309)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.61/0.59  % (9303)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.61/0.59  % (9283)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.61/0.60  % (9289)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.61/0.60  fof(f24,plain,(
% 1.61/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2) | k7_setfam_1(X0,X1) != X2) )),
% 1.61/0.60    inference(cnf_transformation,[],[f13])).
% 1.61/0.60  fof(f72,plain,(
% 1.61/0.60    ~r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1)) | spl4_1),
% 1.61/0.60    inference(avatar_component_clause,[],[f71])).
% 1.61/0.60  fof(f77,plain,(
% 1.61/0.60    r2_hidden(sK2,sK1) | ~spl4_2),
% 1.61/0.60    inference(avatar_component_clause,[],[f75])).
% 1.61/0.60  fof(f84,plain,(
% 1.61/0.60    ~spl4_1 | ~spl4_2),
% 1.61/0.60    inference(avatar_split_clause,[],[f18,f75,f71])).
% 1.61/0.60  fof(f18,plain,(
% 1.61/0.60    ~r2_hidden(sK2,sK1) | ~r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1))),
% 1.61/0.60    inference(cnf_transformation,[],[f10])).
% 1.61/0.60  fof(f78,plain,(
% 1.61/0.60    spl4_1 | spl4_2),
% 1.61/0.60    inference(avatar_split_clause,[],[f17,f75,f71])).
% 1.61/0.60  fof(f17,plain,(
% 1.61/0.60    r2_hidden(sK2,sK1) | r2_hidden(k3_subset_1(sK0,sK2),k7_setfam_1(sK0,sK1))),
% 1.61/0.60    inference(cnf_transformation,[],[f10])).
% 1.61/0.60  % SZS output end Proof for theBenchmark
% 1.61/0.60  % (9286)------------------------------
% 1.61/0.60  % (9286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.60  % (9286)Termination reason: Refutation
% 1.61/0.60  
% 1.61/0.60  % (9286)Memory used [KB]: 6268
% 1.61/0.60  % (9286)Time elapsed: 0.153 s
% 1.61/0.60  % (9286)------------------------------
% 1.61/0.60  % (9286)------------------------------
% 1.61/0.60  % (9285)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.61/0.60  % (9281)Success in time 0.236 s
%------------------------------------------------------------------------------
