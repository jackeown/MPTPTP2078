%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:56 EST 2020

% Result     : Theorem 1.87s
% Output     : Refutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   34 (  81 expanded)
%              Number of leaves         :    7 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :   98 ( 333 expanded)
%              Number of equality atoms :   45 ( 150 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f16,f95,f62,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f62,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f17,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_tarski(X1,X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f30,f18])).

fof(f18,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f17,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f95,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(unit_resulting_resolution,[],[f16,f92])).

fof(f92,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,sK0)
      | X3 = X4 ) ),
    inference(duplicate_literal_removal,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X3] :
      ( X3 = X4
      | ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(superposition,[],[f60,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_funct_1(sK1(sK0),X1) = X0
      | ~ r2_hidden(X1,sK0) ) ),
    inference(superposition,[],[f31,f51])).

fof(f51,plain,(
    ! [X0] : sK1(sK0) = sK4(sK0,X0) ),
    inference(unit_resulting_resolution,[],[f21,f20,f22,f33,f32,f34,f15])).

fof(f15,plain,(
    ! [X2,X1] :
      ( k1_relat_1(X2) != sK0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X1) != sK0
      | ~ v1_relat_1(X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k1_relat_1(X2) = X0
                    & k1_relat_1(X1) = X0 )
                 => X1 = X2 ) ) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).

fof(f34,plain,(
    ! [X0,X1] : k1_relat_1(sK4(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f32,plain,(
    ! [X0,X1] : v1_relat_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1] : v1_funct_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f22,plain,(
    ! [X0] : k1_relat_1(sK1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f20,plain,(
    ! [X0] : v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X0] : v1_funct_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK4(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f16,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:12:37 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.21/0.54  % (14014)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.56  % (14030)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.57  % (14008)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.57  % (14009)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.57  % (14008)Refutation not found, incomplete strategy% (14008)------------------------------
% 0.21/0.57  % (14008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (14008)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (14008)Memory used [KB]: 1663
% 0.21/0.57  % (14008)Time elapsed: 0.144 s
% 0.21/0.57  % (14008)------------------------------
% 0.21/0.57  % (14008)------------------------------
% 0.21/0.57  % (14022)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.57  % (14019)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (14019)Refutation not found, incomplete strategy% (14019)------------------------------
% 0.21/0.57  % (14019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (14019)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (14019)Memory used [KB]: 10618
% 0.21/0.57  % (14019)Time elapsed: 0.147 s
% 0.21/0.57  % (14019)------------------------------
% 0.21/0.57  % (14019)------------------------------
% 0.21/0.58  % (14013)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.58  % (14020)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.60/0.59  % (14017)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.60/0.59  % (14010)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.60/0.59  % (14032)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.60/0.59  % (14012)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.60/0.60  % (14011)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.60/0.60  % (14036)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.87/0.60  % (14024)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.87/0.60  % (14017)Refutation not found, incomplete strategy% (14017)------------------------------
% 1.87/0.60  % (14017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.60  % (14031)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.87/0.60  % (14017)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.60  
% 1.87/0.60  % (14017)Memory used [KB]: 10618
% 1.87/0.60  % (14017)Time elapsed: 0.166 s
% 1.87/0.60  % (14017)------------------------------
% 1.87/0.60  % (14017)------------------------------
% 1.87/0.60  % (14035)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.87/0.60  % (14029)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.87/0.61  % (14033)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.87/0.61  % (14027)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.87/0.61  % (14023)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.87/0.61  % (14025)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.87/0.61  % (14025)Refutation not found, incomplete strategy% (14025)------------------------------
% 1.87/0.61  % (14025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.61  % (14025)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.61  
% 1.87/0.61  % (14025)Memory used [KB]: 10618
% 1.87/0.61  % (14025)Time elapsed: 0.192 s
% 1.87/0.61  % (14025)------------------------------
% 1.87/0.61  % (14025)------------------------------
% 1.87/0.62  % (14032)Refutation found. Thanks to Tanya!
% 1.87/0.62  % SZS status Theorem for theBenchmark
% 1.87/0.62  % SZS output start Proof for theBenchmark
% 1.87/0.62  fof(f114,plain,(
% 1.87/0.62    $false),
% 1.87/0.62    inference(unit_resulting_resolution,[],[f16,f95,f62,f23])).
% 1.87/0.62  fof(f23,plain,(
% 1.87/0.62    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0) | X0 = X1) )),
% 1.87/0.62    inference(cnf_transformation,[],[f13])).
% 1.87/0.62  fof(f13,plain,(
% 1.87/0.62    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.87/0.62    inference(ennf_transformation,[],[f1])).
% 1.87/0.62  fof(f1,axiom,(
% 1.87/0.62    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 1.87/0.62  fof(f62,plain,(
% 1.87/0.62    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.87/0.62    inference(unit_resulting_resolution,[],[f17,f39])).
% 1.87/0.62  fof(f39,plain,(
% 1.87/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k2_tarski(X1,X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 1.87/0.62    inference(definition_unfolding,[],[f30,f18])).
% 1.87/0.62  fof(f18,plain,(
% 1.87/0.62    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f4])).
% 1.87/0.62  fof(f4,axiom,(
% 1.87/0.62    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.87/0.62  fof(f30,plain,(
% 1.87/0.62    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 1.87/0.62    inference(cnf_transformation,[],[f5])).
% 1.87/0.62  fof(f5,axiom,(
% 1.87/0.62    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.87/0.62  fof(f17,plain,(
% 1.87/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f2])).
% 1.87/0.62  fof(f2,axiom,(
% 1.87/0.62    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.87/0.62  fof(f95,plain,(
% 1.87/0.62    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 1.87/0.62    inference(unit_resulting_resolution,[],[f16,f92])).
% 1.87/0.62  fof(f92,plain,(
% 1.87/0.62    ( ! [X4,X2,X3] : (~r2_hidden(X2,sK0) | X3 = X4) )),
% 1.87/0.62    inference(duplicate_literal_removal,[],[f67])).
% 1.87/0.62  fof(f67,plain,(
% 1.87/0.62    ( ! [X4,X2,X3] : (X3 = X4 | ~r2_hidden(X2,sK0) | ~r2_hidden(X2,sK0)) )),
% 1.87/0.62    inference(superposition,[],[f60,f60])).
% 1.87/0.62  fof(f60,plain,(
% 1.87/0.62    ( ! [X0,X1] : (k1_funct_1(sK1(sK0),X1) = X0 | ~r2_hidden(X1,sK0)) )),
% 1.87/0.62    inference(superposition,[],[f31,f51])).
% 1.87/0.62  fof(f51,plain,(
% 1.87/0.62    ( ! [X0] : (sK1(sK0) = sK4(sK0,X0)) )),
% 1.87/0.62    inference(unit_resulting_resolution,[],[f21,f20,f22,f33,f32,f34,f15])).
% 1.87/0.62  fof(f15,plain,(
% 1.87/0.62    ( ! [X2,X1] : (k1_relat_1(X2) != sK0 | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X1) != sK0 | ~v1_relat_1(X1) | X1 = X2) )),
% 1.87/0.62    inference(cnf_transformation,[],[f11])).
% 1.87/0.62  fof(f11,plain,(
% 1.87/0.62    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.87/0.62    inference(flattening,[],[f10])).
% 1.87/0.62  fof(f10,plain,(
% 1.87/0.62    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 1.87/0.62    inference(ennf_transformation,[],[f9])).
% 1.87/0.62  fof(f9,negated_conjecture,(
% 1.87/0.62    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 1.87/0.62    inference(negated_conjecture,[],[f8])).
% 1.87/0.62  fof(f8,conjecture,(
% 1.87/0.62    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).
% 1.87/0.62  fof(f34,plain,(
% 1.87/0.62    ( ! [X0,X1] : (k1_relat_1(sK4(X0,X1)) = X0) )),
% 1.87/0.62    inference(cnf_transformation,[],[f14])).
% 1.87/0.62  fof(f14,plain,(
% 1.87/0.62    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.87/0.62    inference(ennf_transformation,[],[f6])).
% 1.87/0.62  fof(f6,axiom,(
% 1.87/0.62    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 1.87/0.62  fof(f32,plain,(
% 1.87/0.62    ( ! [X0,X1] : (v1_relat_1(sK4(X0,X1))) )),
% 1.87/0.62    inference(cnf_transformation,[],[f14])).
% 1.87/0.62  fof(f33,plain,(
% 1.87/0.62    ( ! [X0,X1] : (v1_funct_1(sK4(X0,X1))) )),
% 1.87/0.62    inference(cnf_transformation,[],[f14])).
% 1.87/0.62  fof(f22,plain,(
% 1.87/0.62    ( ! [X0] : (k1_relat_1(sK1(X0)) = X0) )),
% 1.87/0.62    inference(cnf_transformation,[],[f12])).
% 1.87/0.62  fof(f12,plain,(
% 1.87/0.62    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.87/0.62    inference(ennf_transformation,[],[f7])).
% 1.87/0.62  fof(f7,axiom,(
% 1.87/0.62    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 1.87/0.62  fof(f20,plain,(
% 1.87/0.62    ( ! [X0] : (v1_relat_1(sK1(X0))) )),
% 1.87/0.62    inference(cnf_transformation,[],[f12])).
% 1.87/0.62  fof(f21,plain,(
% 1.87/0.62    ( ! [X0] : (v1_funct_1(sK1(X0))) )),
% 1.87/0.62    inference(cnf_transformation,[],[f12])).
% 1.87/0.62  fof(f31,plain,(
% 1.87/0.62    ( ! [X0,X3,X1] : (k1_funct_1(sK4(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f14])).
% 1.87/0.62  fof(f16,plain,(
% 1.87/0.62    k1_xboole_0 != sK0),
% 1.87/0.62    inference(cnf_transformation,[],[f11])).
% 1.87/0.62  % SZS output end Proof for theBenchmark
% 1.87/0.62  % (14032)------------------------------
% 1.87/0.62  % (14032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.62  % (14032)Termination reason: Refutation
% 1.87/0.62  
% 1.87/0.62  % (14032)Memory used [KB]: 6268
% 1.87/0.62  % (14032)Time elapsed: 0.193 s
% 1.87/0.62  % (14032)------------------------------
% 1.87/0.62  % (14032)------------------------------
% 1.87/0.62  % (14007)Success in time 0.254 s
%------------------------------------------------------------------------------
