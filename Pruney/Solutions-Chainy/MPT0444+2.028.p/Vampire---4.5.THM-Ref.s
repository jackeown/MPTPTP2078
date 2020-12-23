%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:04 EST 2020

% Result     : Theorem 1.73s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 101 expanded)
%              Number of leaves         :   15 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  147 ( 274 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f396,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f142,f227,f236,f242,f395])).

fof(f395,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f375])).

fof(f375,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f70,f235,f206,f207])).

fof(f207,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X2,X3)))
      | r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X3) ) ),
    inference(resolution,[],[f97,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f206,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) ),
    inference(resolution,[],[f89,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f89,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f235,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl4_4
  <=> r1_tarski(k3_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f70,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f242,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f238,f60])).

fof(f60,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f48,f47])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

% (27735)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f48,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

fof(f238,plain,
    ( ~ v1_relat_1(sK0)
    | spl4_3 ),
    inference(resolution,[],[f231,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f231,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl4_3
  <=> v1_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f236,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | spl4_2 ),
    inference(avatar_split_clause,[],[f221,f139,f233,f229])).

fof(f139,plain,
    ( spl4_2
  <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f221,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl4_2 ),
    inference(subsumption_resolution,[],[f218,f61])).

fof(f61,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f218,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl4_2 ),
    inference(resolution,[],[f67,f141])).

fof(f141,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f139])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f227,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f223,f60])).

fof(f223,plain,
    ( ~ v1_relat_1(sK0)
    | spl4_1 ),
    inference(resolution,[],[f220,f72])).

fof(f220,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f219,f60])).

fof(f219,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f217,f70])).

fof(f217,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl4_1 ),
    inference(resolution,[],[f67,f137])).

fof(f137,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl4_1
  <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f142,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f133,f139,f135])).

fof(f133,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0)) ),
    inference(resolution,[],[f96,f62])).

fof(f62,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n001.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:52:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.55  % (27728)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.56  % (27718)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.56  % (27717)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.49/0.56  % (27716)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.49/0.56  % (27720)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.49/0.57  % (27734)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.49/0.57  % (27714)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.49/0.57  % (27724)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.49/0.57  % (27720)Refutation not found, incomplete strategy% (27720)------------------------------
% 1.49/0.57  % (27720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.58  % (27726)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.73/0.58  % (27731)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.73/0.58  % (27715)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.73/0.58  % (27732)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.73/0.58  % (27720)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.58  
% 1.73/0.58  % (27720)Memory used [KB]: 10618
% 1.73/0.58  % (27720)Time elapsed: 0.147 s
% 1.73/0.58  % (27720)------------------------------
% 1.73/0.58  % (27720)------------------------------
% 1.73/0.58  % (27733)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.73/0.58  % (27725)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.73/0.58  % (27730)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.73/0.59  % (27739)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.73/0.59  % (27737)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.73/0.59  % (27736)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.73/0.59  % (27719)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.73/0.60  % (27729)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.73/0.60  % (27723)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.73/0.60  % (27728)Refutation found. Thanks to Tanya!
% 1.73/0.60  % SZS status Theorem for theBenchmark
% 1.73/0.60  % SZS output start Proof for theBenchmark
% 1.73/0.60  fof(f396,plain,(
% 1.73/0.60    $false),
% 1.73/0.60    inference(avatar_sat_refutation,[],[f142,f227,f236,f242,f395])).
% 1.73/0.60  fof(f395,plain,(
% 1.73/0.60    spl4_4),
% 1.73/0.60    inference(avatar_contradiction_clause,[],[f375])).
% 1.73/0.60  fof(f375,plain,(
% 1.73/0.60    $false | spl4_4),
% 1.73/0.60    inference(unit_resulting_resolution,[],[f70,f235,f206,f207])).
% 1.73/0.60  fof(f207,plain,(
% 1.73/0.60    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X2,X3))) | r1_tarski(X0,X1) | ~r1_tarski(X0,X3)) )),
% 1.73/0.60    inference(resolution,[],[f97,f90])).
% 1.73/0.60  fof(f90,plain,(
% 1.73/0.60    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f37])).
% 1.73/0.60  fof(f37,plain,(
% 1.73/0.60    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.73/0.60    inference(ennf_transformation,[],[f14])).
% 1.73/0.60  fof(f14,axiom,(
% 1.73/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 1.73/0.60  fof(f97,plain,(
% 1.73/0.60    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | r1_tarski(X0,X1) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.73/0.60    inference(cnf_transformation,[],[f46])).
% 1.73/0.60  fof(f46,plain,(
% 1.73/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.73/0.60    inference(flattening,[],[f45])).
% 1.73/0.60  fof(f45,plain,(
% 1.73/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 1.73/0.60    inference(ennf_transformation,[],[f13])).
% 1.73/0.60  fof(f13,axiom,(
% 1.73/0.60    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 1.73/0.60  fof(f206,plain,(
% 1.73/0.60    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2))) )),
% 1.73/0.60    inference(resolution,[],[f89,f94])).
% 1.73/0.60  fof(f94,plain,(
% 1.73/0.60    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f40])).
% 1.73/0.60  fof(f40,plain,(
% 1.73/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.73/0.60    inference(ennf_transformation,[],[f5])).
% 1.73/0.60  fof(f5,axiom,(
% 1.73/0.60    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.73/0.60  fof(f89,plain,(
% 1.73/0.60    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 1.73/0.60    inference(cnf_transformation,[],[f9])).
% 1.73/0.60  fof(f9,axiom,(
% 1.73/0.60    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
% 1.73/0.60  fof(f235,plain,(
% 1.73/0.60    ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | spl4_4),
% 1.73/0.60    inference(avatar_component_clause,[],[f233])).
% 1.73/0.60  fof(f233,plain,(
% 1.73/0.60    spl4_4 <=> r1_tarski(k3_xboole_0(sK0,sK1),sK1)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.73/0.60  fof(f70,plain,(
% 1.73/0.60    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f6])).
% 1.73/0.60  fof(f6,axiom,(
% 1.73/0.60    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.73/0.60  fof(f242,plain,(
% 1.73/0.60    spl4_3),
% 1.73/0.60    inference(avatar_contradiction_clause,[],[f241])).
% 1.73/0.60  fof(f241,plain,(
% 1.73/0.60    $false | spl4_3),
% 1.73/0.60    inference(subsumption_resolution,[],[f238,f60])).
% 1.73/0.60  fof(f60,plain,(
% 1.73/0.60    v1_relat_1(sK0)),
% 1.73/0.60    inference(cnf_transformation,[],[f49])).
% 1.73/0.60  fof(f49,plain,(
% 1.73/0.60    (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 1.73/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f48,f47])).
% 1.73/0.60  fof(f47,plain,(
% 1.73/0.60    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 1.73/0.60    introduced(choice_axiom,[])).
% 1.73/0.60  % (27735)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.73/0.60  fof(f48,plain,(
% 1.73/0.60    ? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) & v1_relat_1(sK1))),
% 1.73/0.60    introduced(choice_axiom,[])).
% 1.73/0.60  fof(f27,plain,(
% 1.73/0.60    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.73/0.60    inference(ennf_transformation,[],[f26])).
% 1.73/0.60  fof(f26,negated_conjecture,(
% 1.73/0.60    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 1.73/0.60    inference(negated_conjecture,[],[f25])).
% 1.73/0.60  fof(f25,conjecture,(
% 1.73/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).
% 1.73/0.60  fof(f238,plain,(
% 1.73/0.60    ~v1_relat_1(sK0) | spl4_3),
% 1.73/0.60    inference(resolution,[],[f231,f72])).
% 1.73/0.60  fof(f72,plain,(
% 1.73/0.60    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f34])).
% 1.73/0.60  fof(f34,plain,(
% 1.73/0.60    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 1.73/0.60    inference(ennf_transformation,[],[f20])).
% 1.73/0.60  fof(f20,axiom,(
% 1.73/0.60    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 1.73/0.60  fof(f231,plain,(
% 1.73/0.60    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | spl4_3),
% 1.73/0.60    inference(avatar_component_clause,[],[f229])).
% 1.73/0.60  fof(f229,plain,(
% 1.73/0.60    spl4_3 <=> v1_relat_1(k3_xboole_0(sK0,sK1))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.73/0.60  fof(f236,plain,(
% 1.73/0.60    ~spl4_3 | ~spl4_4 | spl4_2),
% 1.73/0.60    inference(avatar_split_clause,[],[f221,f139,f233,f229])).
% 1.73/0.60  fof(f139,plain,(
% 1.73/0.60    spl4_2 <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.73/0.60  fof(f221,plain,(
% 1.73/0.60    ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | spl4_2),
% 1.73/0.60    inference(subsumption_resolution,[],[f218,f61])).
% 1.73/0.60  fof(f61,plain,(
% 1.73/0.60    v1_relat_1(sK1)),
% 1.73/0.60    inference(cnf_transformation,[],[f49])).
% 1.73/0.60  fof(f218,plain,(
% 1.73/0.60    ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | spl4_2),
% 1.73/0.60    inference(resolution,[],[f67,f141])).
% 1.73/0.60  fof(f141,plain,(
% 1.73/0.60    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1)) | spl4_2),
% 1.73/0.60    inference(avatar_component_clause,[],[f139])).
% 1.73/0.60  fof(f67,plain,(
% 1.73/0.60    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f31])).
% 1.73/0.60  fof(f31,plain,(
% 1.73/0.60    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.73/0.60    inference(flattening,[],[f30])).
% 1.73/0.60  fof(f30,plain,(
% 1.73/0.60    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.73/0.60    inference(ennf_transformation,[],[f24])).
% 1.73/0.60  fof(f24,axiom,(
% 1.73/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 1.73/0.60  fof(f227,plain,(
% 1.73/0.60    spl4_1),
% 1.73/0.60    inference(avatar_contradiction_clause,[],[f226])).
% 1.73/0.60  fof(f226,plain,(
% 1.73/0.60    $false | spl4_1),
% 1.73/0.60    inference(subsumption_resolution,[],[f223,f60])).
% 1.73/0.60  fof(f223,plain,(
% 1.73/0.60    ~v1_relat_1(sK0) | spl4_1),
% 1.73/0.60    inference(resolution,[],[f220,f72])).
% 1.73/0.60  fof(f220,plain,(
% 1.73/0.60    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | spl4_1),
% 1.73/0.60    inference(subsumption_resolution,[],[f219,f60])).
% 1.73/0.60  fof(f219,plain,(
% 1.73/0.60    ~v1_relat_1(sK0) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | spl4_1),
% 1.73/0.60    inference(subsumption_resolution,[],[f217,f70])).
% 1.73/0.60  fof(f217,plain,(
% 1.73/0.60    ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | spl4_1),
% 1.73/0.60    inference(resolution,[],[f67,f137])).
% 1.73/0.60  fof(f137,plain,(
% 1.73/0.60    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0)) | spl4_1),
% 1.73/0.60    inference(avatar_component_clause,[],[f135])).
% 1.73/0.60  fof(f135,plain,(
% 1.73/0.60    spl4_1 <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.73/0.60  fof(f142,plain,(
% 1.73/0.60    ~spl4_1 | ~spl4_2),
% 1.73/0.60    inference(avatar_split_clause,[],[f133,f139,f135])).
% 1.73/0.60  fof(f133,plain,(
% 1.73/0.60    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1)) | ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0))),
% 1.73/0.60    inference(resolution,[],[f96,f62])).
% 1.73/0.60  fof(f62,plain,(
% 1.73/0.60    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),
% 1.73/0.60    inference(cnf_transformation,[],[f49])).
% 1.73/0.60  fof(f96,plain,(
% 1.73/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f44])).
% 1.73/0.60  fof(f44,plain,(
% 1.73/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.73/0.60    inference(flattening,[],[f43])).
% 1.73/0.60  fof(f43,plain,(
% 1.73/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.73/0.60    inference(ennf_transformation,[],[f7])).
% 1.73/0.60  fof(f7,axiom,(
% 1.73/0.60    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.73/0.60  % SZS output end Proof for theBenchmark
% 1.73/0.60  % (27728)------------------------------
% 1.73/0.60  % (27728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.60  % (27728)Termination reason: Refutation
% 1.73/0.60  
% 1.73/0.60  % (27728)Memory used [KB]: 6524
% 1.73/0.60  % (27728)Time elapsed: 0.163 s
% 1.73/0.60  % (27728)------------------------------
% 1.73/0.60  % (27728)------------------------------
% 1.73/0.61  % (27713)Success in time 0.244 s
%------------------------------------------------------------------------------
