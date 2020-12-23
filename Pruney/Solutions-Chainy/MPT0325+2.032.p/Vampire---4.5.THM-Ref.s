%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:42 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 507 expanded)
%              Number of leaves         :    7 ( 147 expanded)
%              Depth                    :   12
%              Number of atoms          :  113 (1337 expanded)
%              Number of equality atoms :   21 ( 152 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f533,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f286,f530])).

fof(f530,plain,(
    spl11_2 ),
    inference(avatar_contradiction_clause,[],[f524])).

fof(f524,plain,
    ( $false
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f466,f466,f464,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f464,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl11_2 ),
    inference(backward_demodulation,[],[f20,f453])).

fof(f453,plain,
    ( k1_xboole_0 = sK1
    | spl11_2 ),
    inference(superposition,[],[f400,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f400,plain,
    ( ! [X0] : sK1 = k2_zfmisc_1(sK1,X0)
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f386,f386,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f386,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f289,f318,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f318,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK4(sK0,sK2),X0),k2_zfmisc_1(sK0,sK1))
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f19,f303,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f303,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(sK4(sK0,sK2),X0),k2_zfmisc_1(sK2,X1))
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f290,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f290,plain,
    ( ~ r2_hidden(sK4(sK0,sK2),sK2)
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f64,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl11_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl11_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

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

fof(f289,plain,
    ( r2_hidden(sK4(sK0,sK2),sK0)
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f64,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f20,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f466,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | spl11_2 ),
    inference(backward_demodulation,[],[f386,f453])).

fof(f286,plain,(
    spl11_1 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f224,f224,f223,f33])).

fof(f223,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl11_1 ),
    inference(backward_demodulation,[],[f20,f212])).

fof(f212,plain,
    ( k1_xboole_0 = sK0
    | spl11_1 ),
    inference(superposition,[],[f151,f46])).

fof(f151,plain,
    ( ! [X0] : sK0 = k2_zfmisc_1(sK0,X0)
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f107,f107,f33])).

fof(f107,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f66,f100,f31])).

fof(f100,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK4(sK1,sK3)),k2_zfmisc_1(sK0,sK1))
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f19,f77,f26])).

fof(f77,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,sK4(sK1,sK3)),k2_zfmisc_1(X1,sK3))
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f67,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f67,plain,
    ( ~ r2_hidden(sK4(sK1,sK3),sK3)
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f60,f28])).

fof(f60,plain,
    ( ~ r1_tarski(sK1,sK3)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl11_1
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f66,plain,
    ( r2_hidden(sK4(sK1,sK3),sK1)
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f60,f27])).

fof(f224,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | spl11_1 ),
    inference(backward_demodulation,[],[f107,f212])).

fof(f65,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f18,f62,f58])).

fof(f18,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:07:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (10358)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (10359)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (10357)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (10367)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (10368)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (10358)Refutation not found, incomplete strategy% (10358)------------------------------
% 0.21/0.52  % (10358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10358)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10358)Memory used [KB]: 10618
% 0.21/0.52  % (10358)Time elapsed: 0.107 s
% 0.21/0.52  % (10358)------------------------------
% 0.21/0.52  % (10358)------------------------------
% 0.21/0.52  % (10364)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (10365)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (10376)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (10355)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (10371)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (10362)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (10384)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (10364)Refutation not found, incomplete strategy% (10364)------------------------------
% 0.21/0.53  % (10364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (10364)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (10364)Memory used [KB]: 10618
% 0.21/0.53  % (10364)Time elapsed: 0.111 s
% 0.21/0.53  % (10364)------------------------------
% 0.21/0.53  % (10364)------------------------------
% 0.21/0.53  % (10380)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (10369)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (10360)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (10379)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (10385)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (10361)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (10372)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (10373)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (10383)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (10381)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (10363)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (10366)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (10382)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (10374)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (10377)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (10378)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (10375)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.56  % (10370)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (10378)Refutation not found, incomplete strategy% (10378)------------------------------
% 0.21/0.56  % (10378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (10373)Refutation not found, incomplete strategy% (10373)------------------------------
% 1.51/0.56  % (10373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (10373)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.56  
% 1.51/0.56  % (10373)Memory used [KB]: 10618
% 1.51/0.56  % (10373)Time elapsed: 0.148 s
% 1.51/0.56  % (10373)------------------------------
% 1.51/0.56  % (10373)------------------------------
% 1.51/0.56  % (10378)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.56  
% 1.51/0.56  % (10378)Memory used [KB]: 10746
% 1.51/0.56  % (10378)Time elapsed: 0.102 s
% 1.51/0.56  % (10378)------------------------------
% 1.51/0.56  % (10378)------------------------------
% 1.51/0.56  % (10360)Refutation found. Thanks to Tanya!
% 1.51/0.56  % SZS status Theorem for theBenchmark
% 1.51/0.56  % SZS output start Proof for theBenchmark
% 1.51/0.56  fof(f533,plain,(
% 1.51/0.56    $false),
% 1.51/0.56    inference(avatar_sat_refutation,[],[f65,f286,f530])).
% 1.51/0.56  fof(f530,plain,(
% 1.51/0.56    spl11_2),
% 1.51/0.56    inference(avatar_contradiction_clause,[],[f524])).
% 1.51/0.56  fof(f524,plain,(
% 1.51/0.56    $false | spl11_2),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f466,f466,f464,f34])).
% 1.51/0.56  fof(f34,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 1.51/0.56    inference(cnf_transformation,[],[f7])).
% 1.51/0.56  fof(f7,axiom,(
% 1.51/0.56    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.51/0.56  fof(f464,plain,(
% 1.51/0.56    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | spl11_2),
% 1.51/0.56    inference(backward_demodulation,[],[f20,f453])).
% 1.51/0.56  fof(f453,plain,(
% 1.51/0.56    k1_xboole_0 = sK1 | spl11_2),
% 1.51/0.56    inference(superposition,[],[f400,f46])).
% 1.51/0.56  fof(f46,plain,(
% 1.51/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.51/0.56    inference(equality_resolution,[],[f23])).
% 1.51/0.56  fof(f23,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f9])).
% 1.51/0.56  fof(f9,axiom,(
% 1.51/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.51/0.56  fof(f400,plain,(
% 1.51/0.56    ( ! [X0] : (sK1 = k2_zfmisc_1(sK1,X0)) ) | spl11_2),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f386,f386,f33])).
% 1.51/0.56  fof(f33,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 1.51/0.56    inference(cnf_transformation,[],[f7])).
% 1.51/0.56  fof(f386,plain,(
% 1.51/0.56    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | spl11_2),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f289,f318,f31])).
% 1.51/0.56  fof(f31,plain,(
% 1.51/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X3) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f8])).
% 1.51/0.56  fof(f8,axiom,(
% 1.51/0.56    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.51/0.56  fof(f318,plain,(
% 1.51/0.56    ( ! [X0] : (~r2_hidden(k4_tarski(sK4(sK0,sK2),X0),k2_zfmisc_1(sK0,sK1))) ) | spl11_2),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f19,f303,f26])).
% 1.51/0.56  fof(f26,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f15])).
% 1.51/0.56  fof(f15,plain,(
% 1.51/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f1])).
% 1.51/0.56  fof(f1,axiom,(
% 1.51/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.51/0.56  fof(f303,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK4(sK0,sK2),X0),k2_zfmisc_1(sK2,X1))) ) | spl11_2),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f290,f29])).
% 1.51/0.56  fof(f29,plain,(
% 1.51/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f8])).
% 1.51/0.56  fof(f290,plain,(
% 1.51/0.56    ~r2_hidden(sK4(sK0,sK2),sK2) | spl11_2),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f64,f28])).
% 1.51/0.56  fof(f28,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f15])).
% 1.51/0.56  fof(f64,plain,(
% 1.51/0.56    ~r1_tarski(sK0,sK2) | spl11_2),
% 1.51/0.56    inference(avatar_component_clause,[],[f62])).
% 1.51/0.56  fof(f62,plain,(
% 1.51/0.56    spl11_2 <=> r1_tarski(sK0,sK2)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.51/0.56  fof(f19,plain,(
% 1.51/0.56    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 1.51/0.56    inference(cnf_transformation,[],[f14])).
% 1.51/0.56  fof(f14,plain,(
% 1.51/0.56    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.51/0.56    inference(flattening,[],[f13])).
% 1.51/0.56  fof(f13,plain,(
% 1.51/0.56    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.51/0.56    inference(ennf_transformation,[],[f11])).
% 1.51/0.56  fof(f11,negated_conjecture,(
% 1.51/0.56    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.51/0.56    inference(negated_conjecture,[],[f10])).
% 1.51/0.56  fof(f10,conjecture,(
% 1.51/0.56    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 1.51/0.56  fof(f289,plain,(
% 1.51/0.56    r2_hidden(sK4(sK0,sK2),sK0) | spl11_2),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f64,f27])).
% 1.51/0.56  fof(f27,plain,(
% 1.51/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f15])).
% 1.51/0.56  fof(f20,plain,(
% 1.51/0.56    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 1.51/0.56    inference(cnf_transformation,[],[f14])).
% 1.51/0.56  fof(f466,plain,(
% 1.51/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | spl11_2),
% 1.51/0.56    inference(backward_demodulation,[],[f386,f453])).
% 1.51/0.56  fof(f286,plain,(
% 1.51/0.56    spl11_1),
% 1.51/0.56    inference(avatar_contradiction_clause,[],[f279])).
% 1.51/0.56  fof(f279,plain,(
% 1.51/0.56    $false | spl11_1),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f224,f224,f223,f33])).
% 1.51/0.56  fof(f223,plain,(
% 1.51/0.56    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | spl11_1),
% 1.51/0.56    inference(backward_demodulation,[],[f20,f212])).
% 1.51/0.56  fof(f212,plain,(
% 1.51/0.56    k1_xboole_0 = sK0 | spl11_1),
% 1.51/0.56    inference(superposition,[],[f151,f46])).
% 1.51/0.56  fof(f151,plain,(
% 1.51/0.56    ( ! [X0] : (sK0 = k2_zfmisc_1(sK0,X0)) ) | spl11_1),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f107,f107,f33])).
% 1.51/0.56  fof(f107,plain,(
% 1.51/0.56    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | spl11_1),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f66,f100,f31])).
% 1.51/0.56  fof(f100,plain,(
% 1.51/0.56    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK4(sK1,sK3)),k2_zfmisc_1(sK0,sK1))) ) | spl11_1),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f19,f77,f26])).
% 1.51/0.56  fof(f77,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,sK4(sK1,sK3)),k2_zfmisc_1(X1,sK3))) ) | spl11_1),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f67,f30])).
% 1.51/0.56  fof(f30,plain,(
% 1.51/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f8])).
% 1.51/0.56  fof(f67,plain,(
% 1.51/0.56    ~r2_hidden(sK4(sK1,sK3),sK3) | spl11_1),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f60,f28])).
% 1.51/0.56  fof(f60,plain,(
% 1.51/0.56    ~r1_tarski(sK1,sK3) | spl11_1),
% 1.51/0.56    inference(avatar_component_clause,[],[f58])).
% 1.51/0.56  fof(f58,plain,(
% 1.51/0.56    spl11_1 <=> r1_tarski(sK1,sK3)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.51/0.56  fof(f66,plain,(
% 1.51/0.56    r2_hidden(sK4(sK1,sK3),sK1) | spl11_1),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f60,f27])).
% 1.51/0.56  fof(f224,plain,(
% 1.51/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | spl11_1),
% 1.51/0.56    inference(backward_demodulation,[],[f107,f212])).
% 1.51/0.56  fof(f65,plain,(
% 1.51/0.56    ~spl11_1 | ~spl11_2),
% 1.51/0.56    inference(avatar_split_clause,[],[f18,f62,f58])).
% 1.51/0.56  fof(f18,plain,(
% 1.51/0.56    ~r1_tarski(sK0,sK2) | ~r1_tarski(sK1,sK3)),
% 1.51/0.56    inference(cnf_transformation,[],[f14])).
% 1.51/0.56  % SZS output end Proof for theBenchmark
% 1.51/0.56  % (10360)------------------------------
% 1.51/0.56  % (10360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (10360)Termination reason: Refutation
% 1.51/0.56  
% 1.51/0.56  % (10360)Memory used [KB]: 6396
% 1.51/0.56  % (10360)Time elapsed: 0.134 s
% 1.51/0.56  % (10360)------------------------------
% 1.51/0.56  % (10360)------------------------------
% 1.51/0.56  % (10352)Success in time 0.205 s
%------------------------------------------------------------------------------
