%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:42 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   43 (  88 expanded)
%              Number of leaves         :    7 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  100 ( 207 expanded)
%              Number of equality atoms :   29 (  67 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f271,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f136,f229])).

fof(f229,plain,(
    ~ spl9_1 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f221,f223])).

fof(f223,plain,
    ( r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl9_1 ),
    inference(forward_demodulation,[],[f222,f22])).

fof(f22,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f222,plain,
    ( r2_hidden(sK1(k1_xboole_0,k3_tarski(k1_xboole_0)),k1_xboole_0)
    | ~ spl9_1 ),
    inference(forward_demodulation,[],[f218,f36])).

fof(f36,plain,(
    k1_xboole_0 = k1_setfam_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X1] :
      ( k1_xboole_0 = X1
      | k1_setfam_1(k1_xboole_0) != X1 ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = X1
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f218,plain,
    ( r2_hidden(sK1(k1_setfam_1(k1_xboole_0),k3_tarski(k1_xboole_0)),k1_setfam_1(k1_xboole_0))
    | ~ spl9_1 ),
    inference(superposition,[],[f42,f55])).

fof(f55,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl9_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f42,plain,(
    r2_hidden(sK1(k1_setfam_1(sK0),k3_tarski(sK0)),k1_setfam_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f13,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f13,plain,(
    ~ r1_tarski(k1_setfam_1(sK0),k3_tarski(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] : ~ r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_setfam_1)).

fof(f221,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl9_1 ),
    inference(forward_demodulation,[],[f220,f36])).

fof(f220,plain,
    ( ~ r2_hidden(sK1(k1_setfam_1(k1_xboole_0),k1_xboole_0),k1_xboole_0)
    | ~ spl9_1 ),
    inference(forward_demodulation,[],[f216,f22])).

fof(f216,plain,
    ( ~ r2_hidden(sK1(k1_setfam_1(k1_xboole_0),k3_tarski(k1_xboole_0)),k3_tarski(k1_xboole_0))
    | ~ spl9_1 ),
    inference(superposition,[],[f43,f55])).

fof(f43,plain,(
    ~ r2_hidden(sK1(k1_setfam_1(sK0),k3_tarski(sK0)),k3_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f13,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f136,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | spl9_1 ),
    inference(subsumption_resolution,[],[f122,f76])).

fof(f76,plain,
    ( r2_hidden(sK1(k1_setfam_1(sK0),k3_tarski(sK0)),sK8(sK0))
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f68,f54,f42,f41])).

fof(f41,plain,(
    ! [X2,X0,X3] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X3)
      | ~ r2_hidden(X2,k1_setfam_1(X0)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X3)
      | ~ r2_hidden(X2,X1)
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f54,plain,
    ( k1_xboole_0 != sK0
    | spl9_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f68,plain,
    ( r2_hidden(sK8(sK0),sK0)
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f54,f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK8(X0),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f122,plain,
    ( ~ r2_hidden(sK1(k1_setfam_1(sK0),k3_tarski(sK0)),sK8(sK0))
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f68,f43,f32])).

fof(f32,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:07:18 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.31/0.54  % (17306)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.31/0.55  % (17323)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.31/0.55  % (17313)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.31/0.55  % (17322)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.46/0.55  % (17304)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.46/0.55  % (17302)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.46/0.55  % (17299)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.46/0.55  % (17308)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.46/0.55  % (17307)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.46/0.55  % (17314)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.46/0.56  % (17306)Refutation not found, incomplete strategy% (17306)------------------------------
% 1.46/0.56  % (17306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (17306)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.56  
% 1.46/0.56  % (17306)Memory used [KB]: 10618
% 1.46/0.56  % (17306)Time elapsed: 0.131 s
% 1.46/0.56  % (17306)------------------------------
% 1.46/0.56  % (17306)------------------------------
% 1.46/0.56  % (17320)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.46/0.56  % (17307)Refutation found. Thanks to Tanya!
% 1.46/0.56  % SZS status Theorem for theBenchmark
% 1.46/0.56  % SZS output start Proof for theBenchmark
% 1.46/0.56  fof(f271,plain,(
% 1.46/0.56    $false),
% 1.46/0.56    inference(avatar_sat_refutation,[],[f136,f229])).
% 1.46/0.56  fof(f229,plain,(
% 1.46/0.56    ~spl9_1),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f228])).
% 1.46/0.56  fof(f228,plain,(
% 1.46/0.56    $false | ~spl9_1),
% 1.46/0.56    inference(subsumption_resolution,[],[f221,f223])).
% 1.46/0.56  fof(f223,plain,(
% 1.46/0.56    r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~spl9_1),
% 1.46/0.56    inference(forward_demodulation,[],[f222,f22])).
% 1.46/0.56  fof(f22,plain,(
% 1.46/0.56    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.46/0.56    inference(cnf_transformation,[],[f4])).
% 1.46/0.56  fof(f4,axiom,(
% 1.46/0.56    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 1.46/0.56  fof(f222,plain,(
% 1.46/0.56    r2_hidden(sK1(k1_xboole_0,k3_tarski(k1_xboole_0)),k1_xboole_0) | ~spl9_1),
% 1.46/0.56    inference(forward_demodulation,[],[f218,f36])).
% 1.46/0.56  fof(f36,plain,(
% 1.46/0.56    k1_xboole_0 = k1_setfam_1(k1_xboole_0)),
% 1.46/0.56    inference(equality_resolution,[],[f35])).
% 1.46/0.56  fof(f35,plain,(
% 1.46/0.56    ( ! [X1] : (k1_xboole_0 = X1 | k1_setfam_1(k1_xboole_0) != X1) )),
% 1.46/0.56    inference(equality_resolution,[],[f30])).
% 1.46/0.56  fof(f30,plain,(
% 1.46/0.56    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = X1 | k1_setfam_1(X0) != X1) )),
% 1.46/0.56    inference(cnf_transformation,[],[f11])).
% 1.46/0.56  fof(f11,plain,(
% 1.46/0.56    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 1.46/0.56    inference(ennf_transformation,[],[f5])).
% 1.46/0.56  fof(f5,axiom,(
% 1.46/0.56    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).
% 1.46/0.56  fof(f218,plain,(
% 1.46/0.56    r2_hidden(sK1(k1_setfam_1(k1_xboole_0),k3_tarski(k1_xboole_0)),k1_setfam_1(k1_xboole_0)) | ~spl9_1),
% 1.46/0.56    inference(superposition,[],[f42,f55])).
% 1.46/0.56  fof(f55,plain,(
% 1.46/0.56    k1_xboole_0 = sK0 | ~spl9_1),
% 1.46/0.56    inference(avatar_component_clause,[],[f53])).
% 1.46/0.56  fof(f53,plain,(
% 1.46/0.56    spl9_1 <=> k1_xboole_0 = sK0),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.46/0.56  fof(f42,plain,(
% 1.46/0.56    r2_hidden(sK1(k1_setfam_1(sK0),k3_tarski(sK0)),k1_setfam_1(sK0))),
% 1.46/0.56    inference(unit_resulting_resolution,[],[f13,f14])).
% 1.46/0.56  fof(f14,plain,(
% 1.46/0.56    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f10])).
% 1.46/0.56  fof(f10,plain,(
% 1.46/0.56    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f8])).
% 1.46/0.56  fof(f8,plain,(
% 1.46/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.46/0.56    inference(unused_predicate_definition_removal,[],[f1])).
% 1.46/0.56  fof(f1,axiom,(
% 1.46/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.46/0.56  fof(f13,plain,(
% 1.46/0.56    ~r1_tarski(k1_setfam_1(sK0),k3_tarski(sK0))),
% 1.46/0.56    inference(cnf_transformation,[],[f9])).
% 1.46/0.56  fof(f9,plain,(
% 1.46/0.56    ? [X0] : ~r1_tarski(k1_setfam_1(X0),k3_tarski(X0))),
% 1.46/0.56    inference(ennf_transformation,[],[f7])).
% 1.46/0.56  fof(f7,negated_conjecture,(
% 1.46/0.56    ~! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0))),
% 1.46/0.56    inference(negated_conjecture,[],[f6])).
% 1.46/0.56  fof(f6,conjecture,(
% 1.46/0.56    ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_setfam_1)).
% 1.46/0.56  fof(f221,plain,(
% 1.46/0.56    ~r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~spl9_1),
% 1.46/0.56    inference(forward_demodulation,[],[f220,f36])).
% 1.46/0.56  fof(f220,plain,(
% 1.46/0.56    ~r2_hidden(sK1(k1_setfam_1(k1_xboole_0),k1_xboole_0),k1_xboole_0) | ~spl9_1),
% 1.46/0.56    inference(forward_demodulation,[],[f216,f22])).
% 1.46/0.56  fof(f216,plain,(
% 1.46/0.56    ~r2_hidden(sK1(k1_setfam_1(k1_xboole_0),k3_tarski(k1_xboole_0)),k3_tarski(k1_xboole_0)) | ~spl9_1),
% 1.46/0.56    inference(superposition,[],[f43,f55])).
% 1.46/0.56  fof(f43,plain,(
% 1.46/0.56    ~r2_hidden(sK1(k1_setfam_1(sK0),k3_tarski(sK0)),k3_tarski(sK0))),
% 1.46/0.56    inference(unit_resulting_resolution,[],[f13,f15])).
% 1.46/0.56  fof(f15,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~r2_hidden(sK1(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f10])).
% 1.46/0.56  fof(f136,plain,(
% 1.46/0.56    spl9_1),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f135])).
% 1.46/0.56  fof(f135,plain,(
% 1.46/0.56    $false | spl9_1),
% 1.46/0.56    inference(subsumption_resolution,[],[f122,f76])).
% 1.46/0.56  fof(f76,plain,(
% 1.46/0.56    r2_hidden(sK1(k1_setfam_1(sK0),k3_tarski(sK0)),sK8(sK0)) | spl9_1),
% 1.46/0.56    inference(unit_resulting_resolution,[],[f68,f54,f42,f41])).
% 1.46/0.56  fof(f41,plain,(
% 1.46/0.56    ( ! [X2,X0,X3] : (k1_xboole_0 = X0 | ~r2_hidden(X3,X0) | r2_hidden(X2,X3) | ~r2_hidden(X2,k1_setfam_1(X0))) )),
% 1.46/0.56    inference(equality_resolution,[],[f26])).
% 1.46/0.56  fof(f26,plain,(
% 1.46/0.56    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | ~r2_hidden(X3,X0) | r2_hidden(X2,X3) | ~r2_hidden(X2,X1) | k1_setfam_1(X0) != X1) )),
% 1.46/0.56    inference(cnf_transformation,[],[f11])).
% 1.46/0.56  fof(f54,plain,(
% 1.46/0.56    k1_xboole_0 != sK0 | spl9_1),
% 1.46/0.56    inference(avatar_component_clause,[],[f53])).
% 1.46/0.56  fof(f68,plain,(
% 1.46/0.56    r2_hidden(sK8(sK0),sK0) | spl9_1),
% 1.46/0.56    inference(unit_resulting_resolution,[],[f54,f31])).
% 1.46/0.56  fof(f31,plain,(
% 1.46/0.56    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK8(X0),X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f12])).
% 1.46/0.56  fof(f12,plain,(
% 1.46/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.46/0.56    inference(ennf_transformation,[],[f2])).
% 1.46/0.56  fof(f2,axiom,(
% 1.46/0.56    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.46/0.56  fof(f122,plain,(
% 1.46/0.56    ~r2_hidden(sK1(k1_setfam_1(sK0),k3_tarski(sK0)),sK8(sK0)) | spl9_1),
% 1.46/0.56    inference(unit_resulting_resolution,[],[f68,f43,f32])).
% 1.46/0.56  fof(f32,plain,(
% 1.46/0.56    ( ! [X2,X0,X3] : (~r2_hidden(X2,X3) | ~r2_hidden(X3,X0) | r2_hidden(X2,k3_tarski(X0))) )),
% 1.46/0.56    inference(equality_resolution,[],[f21])).
% 1.46/0.56  fof(f21,plain,(
% 1.46/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X2,X3) | ~r2_hidden(X3,X0) | r2_hidden(X2,X1) | k3_tarski(X0) != X1) )),
% 1.46/0.56    inference(cnf_transformation,[],[f3])).
% 1.46/0.56  fof(f3,axiom,(
% 1.46/0.56    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 1.46/0.56  % SZS output end Proof for theBenchmark
% 1.46/0.56  % (17307)------------------------------
% 1.46/0.56  % (17307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (17307)Termination reason: Refutation
% 1.46/0.56  
% 1.46/0.56  % (17307)Memory used [KB]: 10746
% 1.46/0.56  % (17307)Time elapsed: 0.134 s
% 1.46/0.56  % (17307)------------------------------
% 1.46/0.56  % (17307)------------------------------
% 1.46/0.56  % (17297)Success in time 0.194 s
%------------------------------------------------------------------------------
