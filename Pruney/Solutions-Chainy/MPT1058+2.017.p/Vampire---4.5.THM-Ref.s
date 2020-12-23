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
% DateTime   : Thu Dec  3 13:07:19 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 114 expanded)
%              Number of leaves         :    5 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :   83 ( 277 expanded)
%              Number of equality atoms :   12 (  65 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f413,plain,(
    $false ),
    inference(subsumption_resolution,[],[f408,f412])).

fof(f412,plain,(
    ~ r2_hidden(sK4(sK1,k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f409,f411])).

fof(f411,plain,(
    r2_hidden(sK4(sK1,k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)),sK1) ),
    inference(subsumption_resolution,[],[f400,f84])).

fof(f84,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k10_relat_1(sK0,sK2))
      | r2_hidden(X3,sK1) ) ),
    inference(resolution,[],[f31,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f31,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(f400,plain,
    ( r2_hidden(sK4(sK1,k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2))
    | r2_hidden(sK4(sK1,k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)),sK1) ),
    inference(resolution,[],[f255,f111])).

fof(f111,plain,(
    ! [X8,X7] :
      ( sQ5_eqProxy(k3_xboole_0(X7,k10_relat_1(sK0,sK2)),X8)
      | r2_hidden(sK4(X7,k10_relat_1(sK0,sK2),X8),X8)
      | r2_hidden(sK4(X7,k10_relat_1(sK0,sK2),X8),sK1) ) ),
    inference(resolution,[],[f84,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | sQ5_eqProxy(k3_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f53,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f255,plain,(
    ~ sQ5_eqProxy(k3_xboole_0(sK1,k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f116,f79])).

fof(f79,plain,(
    ! [X0,X1] : sQ5_eqProxy(k10_relat_1(k7_relat_1(sK0,X0),X1),k3_xboole_0(X0,k10_relat_1(sK0,X1))) ),
    inference(resolution,[],[f33,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | sQ5_eqProxy(k10_relat_1(k7_relat_1(X2,X0),X1),k3_xboole_0(X0,k10_relat_1(X2,X1))) ) ),
    inference(equality_proxy_replacement,[],[f48,f61])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f33,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f116,plain,(
    ! [X0] :
      ( ~ sQ5_eqProxy(k10_relat_1(k7_relat_1(sK0,sK1),sK2),X0)
      | ~ sQ5_eqProxy(X0,k10_relat_1(sK0,sK2)) ) ),
    inference(resolution,[],[f85,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ sQ5_eqProxy(X0,X1)
      | ~ sQ5_eqProxy(X1,X2)
      | sQ5_eqProxy(X0,X2) ) ),
    inference(equality_proxy_axiom,[],[f61])).

fof(f85,plain,(
    ~ sQ5_eqProxy(k10_relat_1(k7_relat_1(sK0,sK1),sK2),k10_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f66,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ sQ5_eqProxy(X0,X1)
      | sQ5_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f61])).

fof(f66,plain,(
    ~ sQ5_eqProxy(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2)) ),
    inference(equality_proxy_replacement,[],[f32,f61])).

fof(f32,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f409,plain,
    ( ~ r2_hidden(sK4(sK1,k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)),sK1)
    | ~ r2_hidden(sK4(sK1,k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) ),
    inference(duplicate_literal_removal,[],[f403])).

fof(f403,plain,
    ( ~ r2_hidden(sK4(sK1,k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)),sK1)
    | ~ r2_hidden(sK4(sK1,k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2))
    | ~ r2_hidden(sK4(sK1,k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f255,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | sQ5_eqProxy(k3_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f51,f61])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f408,plain,(
    r2_hidden(sK4(sK1,k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) ),
    inference(duplicate_literal_removal,[],[f405])).

fof(f405,plain,
    ( r2_hidden(sK4(sK1,k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2))
    | r2_hidden(sK4(sK1,k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f255,f73])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:54:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (16861)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (16876)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (16877)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (16860)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (16880)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (16858)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (16863)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (16880)Refutation not found, incomplete strategy% (16880)------------------------------
% 0.21/0.51  % (16880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (16880)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (16880)Memory used [KB]: 10746
% 0.21/0.51  % (16880)Time elapsed: 0.061 s
% 0.21/0.51  % (16880)------------------------------
% 0.21/0.51  % (16880)------------------------------
% 0.21/0.52  % (16867)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (16867)Refutation not found, incomplete strategy% (16867)------------------------------
% 0.21/0.52  % (16867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (16867)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (16867)Memory used [KB]: 10618
% 0.21/0.52  % (16867)Time elapsed: 0.106 s
% 0.21/0.52  % (16867)------------------------------
% 0.21/0.52  % (16867)------------------------------
% 1.21/0.52  % (16865)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.21/0.53  % (16857)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.21/0.53  % (16859)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.21/0.54  % (16866)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.21/0.54  % (16862)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.40/0.54  % (16871)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.40/0.54  % (16868)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.40/0.54  % (16885)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.40/0.54  % (16868)Refutation not found, incomplete strategy% (16868)------------------------------
% 1.40/0.54  % (16868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (16868)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (16868)Memory used [KB]: 10618
% 1.40/0.54  % (16868)Time elapsed: 0.140 s
% 1.40/0.54  % (16868)------------------------------
% 1.40/0.54  % (16868)------------------------------
% 1.40/0.54  % (16874)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.40/0.54  % (16886)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.40/0.54  % (16882)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.40/0.55  % (16879)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.40/0.55  % (16864)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.40/0.55  % (16875)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.40/0.55  % (16873)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.40/0.55  % (16887)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.40/0.55  % (16878)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.40/0.55  % (16872)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.40/0.56  % (16881)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.40/0.56  % (16884)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.40/0.56  % (16878)Refutation not found, incomplete strategy% (16878)------------------------------
% 1.40/0.56  % (16878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.57  % (16878)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.57  
% 1.40/0.57  % (16878)Memory used [KB]: 10874
% 1.40/0.57  % (16878)Time elapsed: 0.157 s
% 1.40/0.57  % (16878)------------------------------
% 1.40/0.57  % (16878)------------------------------
% 1.40/0.57  % (16871)Refutation found. Thanks to Tanya!
% 1.40/0.57  % SZS status Theorem for theBenchmark
% 1.40/0.57  % SZS output start Proof for theBenchmark
% 1.40/0.57  fof(f413,plain,(
% 1.40/0.57    $false),
% 1.40/0.57    inference(subsumption_resolution,[],[f408,f412])).
% 1.40/0.57  fof(f412,plain,(
% 1.40/0.57    ~r2_hidden(sK4(sK1,k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2))),
% 1.40/0.57    inference(subsumption_resolution,[],[f409,f411])).
% 1.40/0.57  fof(f411,plain,(
% 1.40/0.57    r2_hidden(sK4(sK1,k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)),sK1)),
% 1.40/0.57    inference(subsumption_resolution,[],[f400,f84])).
% 1.40/0.57  fof(f84,plain,(
% 1.40/0.57    ( ! [X3] : (~r2_hidden(X3,k10_relat_1(sK0,sK2)) | r2_hidden(X3,sK1)) )),
% 1.40/0.57    inference(resolution,[],[f31,f43])).
% 1.40/0.57  fof(f43,plain,(
% 1.40/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.40/0.57    inference(cnf_transformation,[],[f25])).
% 1.40/0.57  fof(f25,plain,(
% 1.40/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.40/0.57    inference(ennf_transformation,[],[f1])).
% 1.40/0.57  fof(f1,axiom,(
% 1.40/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.40/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.40/0.57  fof(f31,plain,(
% 1.40/0.57    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 1.40/0.57    inference(cnf_transformation,[],[f22])).
% 1.40/0.57  fof(f22,plain,(
% 1.40/0.57    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_relat_1(X0))),
% 1.40/0.57    inference(ennf_transformation,[],[f21])).
% 1.40/0.57  fof(f21,plain,(
% 1.40/0.57    ~! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.40/0.57    inference(pure_predicate_removal,[],[f19])).
% 1.40/0.57  fof(f19,negated_conjecture,(
% 1.40/0.57    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.40/0.57    inference(negated_conjecture,[],[f18])).
% 1.40/0.57  fof(f18,conjecture,(
% 1.40/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.40/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).
% 1.40/0.57  fof(f400,plain,(
% 1.40/0.57    r2_hidden(sK4(sK1,k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) | r2_hidden(sK4(sK1,k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)),sK1)),
% 1.40/0.57    inference(resolution,[],[f255,f111])).
% 1.40/0.57  fof(f111,plain,(
% 1.40/0.57    ( ! [X8,X7] : (sQ5_eqProxy(k3_xboole_0(X7,k10_relat_1(sK0,sK2)),X8) | r2_hidden(sK4(X7,k10_relat_1(sK0,sK2),X8),X8) | r2_hidden(sK4(X7,k10_relat_1(sK0,sK2),X8),sK1)) )),
% 1.40/0.57    inference(resolution,[],[f84,f73])).
% 1.40/0.57  fof(f73,plain,(
% 1.40/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | sQ5_eqProxy(k3_xboole_0(X0,X1),X2)) )),
% 1.40/0.57    inference(equality_proxy_replacement,[],[f53,f61])).
% 1.40/0.57  fof(f61,plain,(
% 1.40/0.57    ! [X1,X0] : (sQ5_eqProxy(X0,X1) <=> X0 = X1)),
% 1.40/0.57    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).
% 1.40/0.57  fof(f53,plain,(
% 1.40/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 1.40/0.57    inference(cnf_transformation,[],[f2])).
% 1.40/0.57  fof(f2,axiom,(
% 1.40/0.57    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.40/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.40/0.57  fof(f255,plain,(
% 1.40/0.57    ~sQ5_eqProxy(k3_xboole_0(sK1,k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2))),
% 1.40/0.57    inference(resolution,[],[f116,f79])).
% 1.40/0.57  fof(f79,plain,(
% 1.40/0.57    ( ! [X0,X1] : (sQ5_eqProxy(k10_relat_1(k7_relat_1(sK0,X0),X1),k3_xboole_0(X0,k10_relat_1(sK0,X1)))) )),
% 1.40/0.57    inference(resolution,[],[f33,f72])).
% 1.40/0.57  fof(f72,plain,(
% 1.40/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | sQ5_eqProxy(k10_relat_1(k7_relat_1(X2,X0),X1),k3_xboole_0(X0,k10_relat_1(X2,X1)))) )),
% 1.40/0.57    inference(equality_proxy_replacement,[],[f48,f61])).
% 1.40/0.57  fof(f48,plain,(
% 1.40/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 1.40/0.57    inference(cnf_transformation,[],[f27])).
% 1.40/0.57  fof(f27,plain,(
% 1.40/0.57    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.40/0.57    inference(ennf_transformation,[],[f16])).
% 1.40/0.57  fof(f16,axiom,(
% 1.40/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.40/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 1.40/0.57  fof(f33,plain,(
% 1.40/0.57    v1_relat_1(sK0)),
% 1.40/0.57    inference(cnf_transformation,[],[f22])).
% 1.40/0.57  fof(f116,plain,(
% 1.40/0.57    ( ! [X0] : (~sQ5_eqProxy(k10_relat_1(k7_relat_1(sK0,sK1),sK2),X0) | ~sQ5_eqProxy(X0,k10_relat_1(sK0,sK2))) )),
% 1.40/0.57    inference(resolution,[],[f85,f78])).
% 1.40/0.57  fof(f78,plain,(
% 1.40/0.57    ( ! [X2,X0,X1] : (~sQ5_eqProxy(X0,X1) | ~sQ5_eqProxy(X1,X2) | sQ5_eqProxy(X0,X2)) )),
% 1.40/0.57    inference(equality_proxy_axiom,[],[f61])).
% 1.40/0.57  fof(f85,plain,(
% 1.40/0.57    ~sQ5_eqProxy(k10_relat_1(k7_relat_1(sK0,sK1),sK2),k10_relat_1(sK0,sK2))),
% 1.40/0.57    inference(resolution,[],[f66,f77])).
% 1.40/0.57  fof(f77,plain,(
% 1.40/0.57    ( ! [X0,X1] : (~sQ5_eqProxy(X0,X1) | sQ5_eqProxy(X1,X0)) )),
% 1.40/0.57    inference(equality_proxy_axiom,[],[f61])).
% 1.40/0.57  fof(f66,plain,(
% 1.40/0.57    ~sQ5_eqProxy(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2))),
% 1.40/0.57    inference(equality_proxy_replacement,[],[f32,f61])).
% 1.40/0.57  fof(f32,plain,(
% 1.40/0.57    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.40/0.57    inference(cnf_transformation,[],[f22])).
% 1.40/0.57  fof(f409,plain,(
% 1.40/0.57    ~r2_hidden(sK4(sK1,k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)),sK1) | ~r2_hidden(sK4(sK1,k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2))),
% 1.40/0.57    inference(duplicate_literal_removal,[],[f403])).
% 1.40/0.57  fof(f403,plain,(
% 1.40/0.57    ~r2_hidden(sK4(sK1,k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)),sK1) | ~r2_hidden(sK4(sK1,k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) | ~r2_hidden(sK4(sK1,k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2))),
% 1.40/0.57    inference(resolution,[],[f255,f75])).
% 1.40/0.57  fof(f75,plain,(
% 1.40/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2) | sQ5_eqProxy(k3_xboole_0(X0,X1),X2)) )),
% 1.40/0.57    inference(equality_proxy_replacement,[],[f51,f61])).
% 1.40/0.57  fof(f51,plain,(
% 1.40/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 1.40/0.57    inference(cnf_transformation,[],[f2])).
% 1.40/0.57  fof(f408,plain,(
% 1.40/0.57    r2_hidden(sK4(sK1,k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2))),
% 1.40/0.57    inference(duplicate_literal_removal,[],[f405])).
% 1.40/0.57  fof(f405,plain,(
% 1.40/0.57    r2_hidden(sK4(sK1,k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) | r2_hidden(sK4(sK1,k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2))),
% 1.40/0.57    inference(resolution,[],[f255,f73])).
% 1.40/0.57  % SZS output end Proof for theBenchmark
% 1.40/0.57  % (16871)------------------------------
% 1.40/0.57  % (16871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.57  % (16871)Termination reason: Refutation
% 1.40/0.57  
% 1.40/0.57  % (16871)Memory used [KB]: 6396
% 1.40/0.57  % (16871)Time elapsed: 0.149 s
% 1.40/0.57  % (16871)------------------------------
% 1.40/0.57  % (16871)------------------------------
% 1.40/0.57  % (16853)Success in time 0.208 s
%------------------------------------------------------------------------------
