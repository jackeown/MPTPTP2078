%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:43 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   45 (  91 expanded)
%              Number of leaves         :    7 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :  100 ( 239 expanded)
%              Number of equality atoms :   12 (  34 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1435,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f604,f1434])).

fof(f1434,plain,(
    spl12_2 ),
    inference(avatar_contradiction_clause,[],[f1423])).

fof(f1423,plain,
    ( $false
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f91,f606,f829,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f829,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK5(sK0,sK2),X0),k2_zfmisc_1(sK0,sK1))
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f19,f655,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f655,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(sK5(sK0,sK2),X0),k2_zfmisc_1(sK2,X1))
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f607,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f607,plain,
    ( ~ r2_hidden(sK5(sK0,sK2),sK2)
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f58,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl12_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl12_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f19,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f606,plain,
    ( r2_hidden(sK5(sK0,sK2),sK0)
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f58,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f91,plain,(
    r2_hidden(sK8(sK0,sK1,sK4(k2_zfmisc_1(sK0,sK1))),sK1) ),
    inference(unit_resulting_resolution,[],[f50,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK8(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK8(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f50,plain,(
    r2_hidden(sK4(k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f20,f21])).

fof(f21,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f20,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f604,plain,(
    spl12_1 ),
    inference(avatar_contradiction_clause,[],[f593])).

fof(f593,plain,
    ( $false
    | spl12_1 ),
    inference(unit_resulting_resolution,[],[f90,f60,f162,f29])).

fof(f162,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK5(sK1,sK3)),k2_zfmisc_1(sK0,sK1))
    | spl12_1 ),
    inference(unit_resulting_resolution,[],[f19,f74,f24])).

fof(f74,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,sK5(sK1,sK3)),k2_zfmisc_1(X1,sK3))
    | spl12_1 ),
    inference(unit_resulting_resolution,[],[f61,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f61,plain,
    ( ~ r2_hidden(sK5(sK1,sK3),sK3)
    | spl12_1 ),
    inference(unit_resulting_resolution,[],[f54,f26])).

fof(f54,plain,
    ( ~ r1_tarski(sK1,sK3)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl12_1
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f60,plain,
    ( r2_hidden(sK5(sK1,sK3),sK1)
    | spl12_1 ),
    inference(unit_resulting_resolution,[],[f54,f25])).

fof(f90,plain,(
    r2_hidden(sK7(sK0,sK1,sK4(k2_zfmisc_1(sK0,sK1))),sK0) ),
    inference(unit_resulting_resolution,[],[f50,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK7(X0,X1,X3),X0)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK7(X0,X1,X3),X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f59,plain,
    ( ~ spl12_1
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f18,f56,f52])).

fof(f18,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:22:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (6342)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (6358)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (6338)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (6335)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (6347)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (6334)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (6331)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (6347)Refutation not found, incomplete strategy% (6347)------------------------------
% 0.21/0.52  % (6347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (6347)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (6347)Memory used [KB]: 10618
% 0.21/0.52  % (6347)Time elapsed: 0.103 s
% 0.21/0.52  % (6347)------------------------------
% 0.21/0.52  % (6347)------------------------------
% 0.21/0.52  % (6337)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (6332)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (6332)Refutation not found, incomplete strategy% (6332)------------------------------
% 0.21/0.52  % (6332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (6332)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (6332)Memory used [KB]: 10618
% 0.21/0.52  % (6332)Time elapsed: 0.107 s
% 0.21/0.52  % (6332)------------------------------
% 0.21/0.52  % (6332)------------------------------
% 0.21/0.52  % (6359)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (6350)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (6338)Refutation not found, incomplete strategy% (6338)------------------------------
% 0.21/0.53  % (6338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6336)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (6333)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (6350)Refutation not found, incomplete strategy% (6350)------------------------------
% 0.21/0.53  % (6350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6350)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (6350)Memory used [KB]: 10746
% 0.21/0.53  % (6350)Time elapsed: 0.125 s
% 0.21/0.53  % (6350)------------------------------
% 0.21/0.53  % (6350)------------------------------
% 0.21/0.53  % (6340)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (6346)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (6338)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (6338)Memory used [KB]: 10618
% 0.21/0.53  % (6338)Time elapsed: 0.110 s
% 0.21/0.53  % (6338)------------------------------
% 0.21/0.53  % (6338)------------------------------
% 0.21/0.53  % (6344)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (6351)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (6349)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (6351)Refutation not found, incomplete strategy% (6351)------------------------------
% 0.21/0.53  % (6351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6351)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (6351)Memory used [KB]: 1663
% 0.21/0.53  % (6351)Time elapsed: 0.124 s
% 0.21/0.53  % (6351)------------------------------
% 0.21/0.53  % (6351)------------------------------
% 0.21/0.53  % (6356)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (6341)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (6352)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (6343)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (6352)Refutation not found, incomplete strategy% (6352)------------------------------
% 0.21/0.54  % (6352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (6352)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (6352)Memory used [KB]: 10746
% 0.21/0.54  % (6352)Time elapsed: 0.098 s
% 0.21/0.54  % (6352)------------------------------
% 0.21/0.54  % (6352)------------------------------
% 0.21/0.54  % (6357)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (6353)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (6348)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (6345)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.47/0.56  % (6355)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.47/0.56  % (6354)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.47/0.56  % (6330)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.47/0.57  % (6339)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.47/0.57  % (6334)Refutation found. Thanks to Tanya!
% 1.47/0.57  % SZS status Theorem for theBenchmark
% 1.62/0.60  % SZS output start Proof for theBenchmark
% 1.62/0.60  fof(f1435,plain,(
% 1.62/0.60    $false),
% 1.62/0.60    inference(avatar_sat_refutation,[],[f59,f604,f1434])).
% 1.62/0.60  fof(f1434,plain,(
% 1.62/0.60    spl12_2),
% 1.62/0.60    inference(avatar_contradiction_clause,[],[f1423])).
% 1.62/0.60  fof(f1423,plain,(
% 1.62/0.60    $false | spl12_2),
% 1.62/0.60    inference(unit_resulting_resolution,[],[f91,f606,f829,f29])).
% 1.62/0.60  fof(f29,plain,(
% 1.62/0.60    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f9])).
% 1.62/0.60  fof(f9,axiom,(
% 1.62/0.60    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.62/0.60  fof(f829,plain,(
% 1.62/0.60    ( ! [X0] : (~r2_hidden(k4_tarski(sK5(sK0,sK2),X0),k2_zfmisc_1(sK0,sK1))) ) | spl12_2),
% 1.62/0.60    inference(unit_resulting_resolution,[],[f19,f655,f24])).
% 1.62/0.60  fof(f24,plain,(
% 1.62/0.60    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f16])).
% 1.62/0.60  fof(f16,plain,(
% 1.62/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.62/0.60    inference(ennf_transformation,[],[f1])).
% 1.62/0.60  fof(f1,axiom,(
% 1.62/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.62/0.60  fof(f655,plain,(
% 1.62/0.60    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK5(sK0,sK2),X0),k2_zfmisc_1(sK2,X1))) ) | spl12_2),
% 1.62/0.60    inference(unit_resulting_resolution,[],[f607,f27])).
% 1.62/0.60  fof(f27,plain,(
% 1.62/0.60    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.62/0.60    inference(cnf_transformation,[],[f9])).
% 1.62/0.60  fof(f607,plain,(
% 1.62/0.60    ~r2_hidden(sK5(sK0,sK2),sK2) | spl12_2),
% 1.62/0.60    inference(unit_resulting_resolution,[],[f58,f26])).
% 1.62/0.60  fof(f26,plain,(
% 1.62/0.60    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f16])).
% 1.62/0.60  fof(f58,plain,(
% 1.62/0.60    ~r1_tarski(sK0,sK2) | spl12_2),
% 1.62/0.60    inference(avatar_component_clause,[],[f56])).
% 1.62/0.60  fof(f56,plain,(
% 1.62/0.60    spl12_2 <=> r1_tarski(sK0,sK2)),
% 1.62/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 1.62/0.60  fof(f19,plain,(
% 1.62/0.60    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 1.62/0.60    inference(cnf_transformation,[],[f14])).
% 1.62/0.60  fof(f14,plain,(
% 1.62/0.60    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.62/0.60    inference(flattening,[],[f13])).
% 1.62/0.60  fof(f13,plain,(
% 1.62/0.60    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.62/0.60    inference(ennf_transformation,[],[f11])).
% 1.62/0.60  fof(f11,negated_conjecture,(
% 1.62/0.60    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.62/0.60    inference(negated_conjecture,[],[f10])).
% 1.62/0.60  fof(f10,conjecture,(
% 1.62/0.60    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 1.62/0.60  fof(f606,plain,(
% 1.62/0.60    r2_hidden(sK5(sK0,sK2),sK0) | spl12_2),
% 1.62/0.60    inference(unit_resulting_resolution,[],[f58,f25])).
% 1.62/0.60  fof(f25,plain,(
% 1.62/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f16])).
% 1.62/0.60  fof(f91,plain,(
% 1.62/0.60    r2_hidden(sK8(sK0,sK1,sK4(k2_zfmisc_1(sK0,sK1))),sK1)),
% 1.62/0.60    inference(unit_resulting_resolution,[],[f50,f48])).
% 1.62/0.60  fof(f48,plain,(
% 1.62/0.60    ( ! [X0,X3,X1] : (r2_hidden(sK8(X0,X1,X3),X1) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 1.62/0.60    inference(equality_resolution,[],[f35])).
% 1.62/0.60  fof(f35,plain,(
% 1.62/0.60    ( ! [X2,X0,X3,X1] : (r2_hidden(sK8(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.62/0.60    inference(cnf_transformation,[],[f8])).
% 1.62/0.60  fof(f8,axiom,(
% 1.62/0.60    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.62/0.60  fof(f50,plain,(
% 1.62/0.60    r2_hidden(sK4(k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))),
% 1.62/0.60    inference(unit_resulting_resolution,[],[f20,f21])).
% 1.62/0.60  fof(f21,plain,(
% 1.62/0.60    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.62/0.60    inference(cnf_transformation,[],[f15])).
% 1.62/0.60  fof(f15,plain,(
% 1.62/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.62/0.60    inference(ennf_transformation,[],[f3])).
% 1.62/0.60  fof(f3,axiom,(
% 1.62/0.60    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.62/0.60  fof(f20,plain,(
% 1.62/0.60    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 1.62/0.60    inference(cnf_transformation,[],[f14])).
% 1.62/0.60  fof(f604,plain,(
% 1.62/0.60    spl12_1),
% 1.62/0.60    inference(avatar_contradiction_clause,[],[f593])).
% 1.62/0.60  fof(f593,plain,(
% 1.62/0.60    $false | spl12_1),
% 1.62/0.60    inference(unit_resulting_resolution,[],[f90,f60,f162,f29])).
% 1.62/0.60  fof(f162,plain,(
% 1.62/0.60    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK5(sK1,sK3)),k2_zfmisc_1(sK0,sK1))) ) | spl12_1),
% 1.62/0.60    inference(unit_resulting_resolution,[],[f19,f74,f24])).
% 1.62/0.60  fof(f74,plain,(
% 1.62/0.60    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,sK5(sK1,sK3)),k2_zfmisc_1(X1,sK3))) ) | spl12_1),
% 1.62/0.60    inference(unit_resulting_resolution,[],[f61,f28])).
% 1.62/0.60  fof(f28,plain,(
% 1.62/0.60    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.62/0.60    inference(cnf_transformation,[],[f9])).
% 1.62/0.60  fof(f61,plain,(
% 1.62/0.60    ~r2_hidden(sK5(sK1,sK3),sK3) | spl12_1),
% 1.62/0.60    inference(unit_resulting_resolution,[],[f54,f26])).
% 1.62/0.60  fof(f54,plain,(
% 1.62/0.60    ~r1_tarski(sK1,sK3) | spl12_1),
% 1.62/0.60    inference(avatar_component_clause,[],[f52])).
% 1.62/0.60  fof(f52,plain,(
% 1.62/0.60    spl12_1 <=> r1_tarski(sK1,sK3)),
% 1.62/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 1.62/0.60  fof(f60,plain,(
% 1.62/0.60    r2_hidden(sK5(sK1,sK3),sK1) | spl12_1),
% 1.62/0.60    inference(unit_resulting_resolution,[],[f54,f25])).
% 1.62/0.60  fof(f90,plain,(
% 1.62/0.60    r2_hidden(sK7(sK0,sK1,sK4(k2_zfmisc_1(sK0,sK1))),sK0)),
% 1.62/0.60    inference(unit_resulting_resolution,[],[f50,f49])).
% 1.62/0.60  fof(f49,plain,(
% 1.62/0.60    ( ! [X0,X3,X1] : (r2_hidden(sK7(X0,X1,X3),X0) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 1.62/0.60    inference(equality_resolution,[],[f34])).
% 1.62/0.60  fof(f34,plain,(
% 1.62/0.60    ( ! [X2,X0,X3,X1] : (r2_hidden(sK7(X0,X1,X3),X0) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.62/0.60    inference(cnf_transformation,[],[f8])).
% 1.62/0.60  fof(f59,plain,(
% 1.62/0.60    ~spl12_1 | ~spl12_2),
% 1.62/0.60    inference(avatar_split_clause,[],[f18,f56,f52])).
% 1.62/0.60  fof(f18,plain,(
% 1.62/0.60    ~r1_tarski(sK0,sK2) | ~r1_tarski(sK1,sK3)),
% 1.62/0.60    inference(cnf_transformation,[],[f14])).
% 1.62/0.60  % SZS output end Proof for theBenchmark
% 1.62/0.60  % (6334)------------------------------
% 1.62/0.60  % (6334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.60  % (6334)Termination reason: Refutation
% 1.62/0.60  
% 1.62/0.60  % (6334)Memory used [KB]: 7036
% 1.62/0.60  % (6334)Time elapsed: 0.151 s
% 1.62/0.60  % (6334)------------------------------
% 1.62/0.60  % (6334)------------------------------
% 1.62/0.60  % (6329)Success in time 0.228 s
%------------------------------------------------------------------------------
