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
% DateTime   : Thu Dec  3 12:55:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 117 expanded)
%              Number of leaves         :   12 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  159 ( 325 expanded)
%              Number of equality atoms :   10 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f216,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f90,f147,f215])).

fof(f215,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f43,f180])).

fof(f180,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0)))
    | spl3_1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f59,f172])).

fof(f172,plain,
    ( sK0 = sK1
    | spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f23,f24,f65,f161,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1)
      | X0 = X1
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f161,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f148,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f148,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f24,f23,f62,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f62,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_2
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f65,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f59,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f24,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f23,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f59,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_1
  <=> r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f43,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f29,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f30,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f147,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f99,f115,f32])).

fof(f115,plain,
    ( r2_hidden(sK0,k1_tarski(sK1))
    | ~ spl3_1
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f102,f58,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f58,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f102,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f93,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f93,plain,
    ( r2_hidden(sK1,sK0)
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f23,f24,f63,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f63,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f99,plain,
    ( r1_tarski(k1_tarski(sK1),sK0)
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f93,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f90,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f42,f61,f57])).

fof(f42,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f21,f29])).

fof(f21,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f64,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f41,f61,f57])).

fof(f41,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f22,f29])).

fof(f22,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:45:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.54  % (14662)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (14654)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (14662)Refutation not found, incomplete strategy% (14662)------------------------------
% 0.22/0.55  % (14662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (14657)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.56  % (14662)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (14662)Memory used [KB]: 10746
% 0.22/0.56  % (14662)Time elapsed: 0.123 s
% 0.22/0.56  % (14662)------------------------------
% 0.22/0.56  % (14662)------------------------------
% 0.22/0.57  % (14658)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.57  % (14661)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.57  % (14671)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.57  % (14670)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.57  % (14655)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.57  % (14681)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.58  % (14655)Refutation not found, incomplete strategy% (14655)------------------------------
% 0.22/0.58  % (14655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (14655)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (14655)Memory used [KB]: 10746
% 0.22/0.58  % (14655)Time elapsed: 0.137 s
% 0.22/0.58  % (14655)------------------------------
% 0.22/0.58  % (14655)------------------------------
% 0.22/0.58  % (14670)Refutation not found, incomplete strategy% (14670)------------------------------
% 0.22/0.58  % (14670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (14656)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.58  % (14670)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (14670)Memory used [KB]: 10618
% 0.22/0.58  % (14670)Time elapsed: 0.136 s
% 0.22/0.58  % (14670)------------------------------
% 0.22/0.58  % (14670)------------------------------
% 0.22/0.58  % (14673)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.58  % (14663)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.58  % (14657)Refutation found. Thanks to Tanya!
% 0.22/0.58  % SZS status Theorem for theBenchmark
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.58  fof(f216,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(avatar_sat_refutation,[],[f64,f90,f147,f215])).
% 0.22/0.58  fof(f215,plain,(
% 0.22/0.58    spl3_1 | ~spl3_2),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f207])).
% 0.22/0.58  fof(f207,plain,(
% 0.22/0.58    $false | (spl3_1 | ~spl3_2)),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f43,f180])).
% 0.22/0.58  fof(f180,plain,(
% 0.22/0.58    ~r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0))) | (spl3_1 | ~spl3_2)),
% 0.22/0.58    inference(backward_demodulation,[],[f59,f172])).
% 0.22/0.58  fof(f172,plain,(
% 0.22/0.58    sK0 = sK1 | (spl3_1 | ~spl3_2)),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f23,f24,f65,f161,f31])).
% 0.22/0.58  fof(f31,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r2_hidden(X0,X1) | X0 = X1 | r2_hidden(X1,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f19])).
% 0.22/0.58  fof(f19,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.58    inference(flattening,[],[f18])).
% 0.22/0.58  fof(f18,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f7])).
% 0.22/0.58  fof(f7,axiom,(
% 0.22/0.58    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.22/0.58  fof(f161,plain,(
% 0.22/0.58    ~r2_hidden(sK1,sK0) | ~spl3_2),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f148,f32])).
% 0.22/0.58  fof(f32,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f20])).
% 0.22/0.58  fof(f20,plain,(
% 0.22/0.58    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.58    inference(ennf_transformation,[],[f9])).
% 0.22/0.58  fof(f9,axiom,(
% 0.22/0.58    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.58  fof(f148,plain,(
% 0.22/0.58    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f24,f23,f62,f26])).
% 0.22/0.58  fof(f26,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f14])).
% 0.22/0.58  fof(f14,plain,(
% 0.22/0.58    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.58    inference(flattening,[],[f13])).
% 0.22/0.58  fof(f13,plain,(
% 0.22/0.58    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f5])).
% 0.22/0.58  fof(f5,axiom,(
% 0.22/0.58    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.22/0.58  fof(f62,plain,(
% 0.22/0.58    r1_ordinal1(sK0,sK1) | ~spl3_2),
% 0.22/0.58    inference(avatar_component_clause,[],[f61])).
% 0.22/0.58  fof(f61,plain,(
% 0.22/0.58    spl3_2 <=> r1_ordinal1(sK0,sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.58  fof(f65,plain,(
% 0.22/0.58    ~r2_hidden(sK0,sK1) | spl3_1),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f59,f45])).
% 0.22/0.58  fof(f45,plain,(
% 0.22/0.58    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 0.22/0.58    inference(equality_resolution,[],[f39])).
% 0.22/0.58  fof(f39,plain,(
% 0.22/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.58    inference(cnf_transformation,[],[f2])).
% 0.22/0.58  fof(f2,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.22/0.58  fof(f24,plain,(
% 0.22/0.58    v3_ordinal1(sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f12])).
% 0.22/0.58  fof(f12,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f11])).
% 0.22/0.58  fof(f11,negated_conjecture,(
% 0.22/0.58    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.22/0.58    inference(negated_conjecture,[],[f10])).
% 0.22/0.58  fof(f10,conjecture,(
% 0.22/0.58    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 0.22/0.58  fof(f23,plain,(
% 0.22/0.58    v3_ordinal1(sK1)),
% 0.22/0.58    inference(cnf_transformation,[],[f12])).
% 0.22/0.58  fof(f59,plain,(
% 0.22/0.58    ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | spl3_1),
% 0.22/0.58    inference(avatar_component_clause,[],[f57])).
% 0.22/0.58  fof(f57,plain,(
% 0.22/0.58    spl3_1 <=> r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.58  fof(f43,plain,(
% 0.22/0.58    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 0.22/0.58    inference(definition_unfolding,[],[f30,f29])).
% 0.22/0.58  fof(f29,plain,(
% 0.22/0.58    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f4])).
% 0.22/0.58  fof(f4,axiom,(
% 0.22/0.58    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.22/0.58  fof(f30,plain,(
% 0.22/0.58    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f6])).
% 0.22/0.58  fof(f6,axiom,(
% 0.22/0.58    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.22/0.58  fof(f147,plain,(
% 0.22/0.58    ~spl3_1 | spl3_2),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f140])).
% 0.22/0.58  fof(f140,plain,(
% 0.22/0.58    $false | (~spl3_1 | spl3_2)),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f99,f115,f32])).
% 0.22/0.58  fof(f115,plain,(
% 0.22/0.58    r2_hidden(sK0,k1_tarski(sK1)) | (~spl3_1 | spl3_2)),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f102,f58,f46])).
% 0.22/0.58  fof(f46,plain,(
% 0.22/0.58    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_xboole_0(X0,X1)) | r2_hidden(X3,X1) | r2_hidden(X3,X0)) )),
% 0.22/0.58    inference(equality_resolution,[],[f38])).
% 0.22/0.58  fof(f38,plain,(
% 0.22/0.58    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.58    inference(cnf_transformation,[],[f2])).
% 0.22/0.58  fof(f58,plain,(
% 0.22/0.58    r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | ~spl3_1),
% 0.22/0.58    inference(avatar_component_clause,[],[f57])).
% 0.22/0.58  fof(f102,plain,(
% 0.22/0.58    ~r2_hidden(sK0,sK1) | spl3_2),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f93,f28])).
% 0.22/0.58  fof(f28,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X1,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f17])).
% 0.22/0.58  fof(f17,plain,(
% 0.22/0.58    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.58    inference(ennf_transformation,[],[f1])).
% 0.22/0.58  fof(f1,axiom,(
% 0.22/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.22/0.58  fof(f93,plain,(
% 0.22/0.58    r2_hidden(sK1,sK0) | spl3_2),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f23,f24,f63,f27])).
% 0.22/0.58  fof(f27,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_ordinal1(X0,X1) | r2_hidden(X1,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f16])).
% 0.22/0.58  fof(f16,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.58    inference(flattening,[],[f15])).
% 0.22/0.58  fof(f15,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f8])).
% 0.22/0.58  fof(f8,axiom,(
% 0.22/0.58    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.22/0.58  fof(f63,plain,(
% 0.22/0.58    ~r1_ordinal1(sK0,sK1) | spl3_2),
% 0.22/0.58    inference(avatar_component_clause,[],[f61])).
% 0.22/0.58  fof(f99,plain,(
% 0.22/0.58    r1_tarski(k1_tarski(sK1),sK0) | spl3_2),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f93,f33])).
% 0.22/0.58  fof(f33,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f3])).
% 0.22/0.58  fof(f3,axiom,(
% 0.22/0.58    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.22/0.58  fof(f90,plain,(
% 0.22/0.58    spl3_1 | spl3_2),
% 0.22/0.58    inference(avatar_split_clause,[],[f42,f61,f57])).
% 0.22/0.58  fof(f42,plain,(
% 0.22/0.58    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 0.22/0.58    inference(definition_unfolding,[],[f21,f29])).
% 0.22/0.58  fof(f21,plain,(
% 0.22/0.58    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.22/0.58    inference(cnf_transformation,[],[f12])).
% 0.22/0.58  fof(f64,plain,(
% 0.22/0.58    ~spl3_1 | ~spl3_2),
% 0.22/0.58    inference(avatar_split_clause,[],[f41,f61,f57])).
% 0.22/0.58  fof(f41,plain,(
% 0.22/0.58    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 0.22/0.58    inference(definition_unfolding,[],[f22,f29])).
% 0.22/0.58  fof(f22,plain,(
% 0.22/0.58    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.22/0.58    inference(cnf_transformation,[],[f12])).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (14657)------------------------------
% 0.22/0.58  % (14657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (14657)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (14657)Memory used [KB]: 6268
% 0.22/0.58  % (14657)Time elapsed: 0.160 s
% 0.22/0.58  % (14657)------------------------------
% 0.22/0.58  % (14657)------------------------------
% 0.22/0.59  % (14652)Success in time 0.218 s
%------------------------------------------------------------------------------
