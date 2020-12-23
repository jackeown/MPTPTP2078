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
% DateTime   : Thu Dec  3 12:53:26 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 173 expanded)
%              Number of leaves         :   11 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  145 ( 448 expanded)
%              Number of equality atoms :   57 ( 187 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f201,plain,(
    $false ),
    inference(global_subsumption,[],[f186,f187])).

fof(f187,plain,(
    r2_hidden(sK3(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0)),k11_relat_1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f162,f55,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(definition_unfolding,[],[f36,f54])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f55,plain,(
    k11_relat_1(sK1,sK0) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(definition_unfolding,[],[f27,f54])).

fof(f27,plain,(
    k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r2_hidden(X0,k1_relat_1(X1))
         => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

fof(f162,plain,(
    k1_xboole_0 != k11_relat_1(sK1,sK0) ),
    inference(superposition,[],[f144,f103])).

fof(f103,plain,(
    ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) ),
    inference(unit_resulting_resolution,[],[f24,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f29,f54])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f144,plain,(
    ! [X2,X0,X1] : k1_xboole_0 != k9_relat_1(sK1,k2_enumset1(X0,X1,X2,sK0)) ),
    inference(unit_resulting_resolution,[],[f24,f130,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(f130,plain,(
    ! [X2,X0,X1] : ~ r1_xboole_0(k1_relat_1(sK1),k2_enumset1(X0,X1,X2,sK0)) ),
    inference(unit_resulting_resolution,[],[f26,f115,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f115,plain,(
    ! [X2,X0,X3,X1] : r2_hidden(X0,k2_enumset1(X1,X2,X3,X0)) ),
    inference(unit_resulting_resolution,[],[f62,f61])).

fof(f61,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,k2_enumset1(X0,X1,X2,X3))
      | ~ sP5(X5,X3,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ sP5(X5,X3,X2,X1,X0)
      | r2_hidden(X5,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X5,X1] : sP5(X5,X5,X2,X1,X0) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X3 != X5
      | sP5(X5,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f26,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f186,plain,(
    ~ r2_hidden(sK3(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0)),k11_relat_1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f24,f185,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(f185,plain,(
    ~ r2_hidden(k4_tarski(sK0,sK3(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0))),sK1) ),
    inference(unit_resulting_resolution,[],[f24,f25,f175,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f175,plain,(
    k1_funct_1(sK1,sK0) != sK3(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f162,f55,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) != X1
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f37,f54])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | sK3(X0,X1) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f25,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:29:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.52  % (347)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (347)Refutation not found, incomplete strategy% (347)------------------------------
% 0.20/0.52  % (347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (341)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (343)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (339)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (342)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (356)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (365)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (347)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (347)Memory used [KB]: 10746
% 0.20/0.53  % (347)Time elapsed: 0.110 s
% 0.20/0.53  % (347)------------------------------
% 0.20/0.53  % (347)------------------------------
% 0.20/0.53  % (340)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (340)Refutation not found, incomplete strategy% (340)------------------------------
% 0.20/0.53  % (340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (340)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (340)Memory used [KB]: 10746
% 0.20/0.53  % (340)Time elapsed: 0.114 s
% 0.20/0.53  % (340)------------------------------
% 0.20/0.53  % (340)------------------------------
% 0.20/0.53  % (361)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (344)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (338)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (360)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (345)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.31/0.54  % (359)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.31/0.54  % (367)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.31/0.54  % (352)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.31/0.54  % (362)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.31/0.55  % (351)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.31/0.55  % (350)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.55  % (357)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.31/0.55  % (362)Refutation found. Thanks to Tanya!
% 1.31/0.55  % SZS status Theorem for theBenchmark
% 1.31/0.55  % SZS output start Proof for theBenchmark
% 1.31/0.55  fof(f201,plain,(
% 1.31/0.55    $false),
% 1.31/0.55    inference(global_subsumption,[],[f186,f187])).
% 1.31/0.55  fof(f187,plain,(
% 1.31/0.55    r2_hidden(sK3(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0)),k11_relat_1(sK1,sK0))),
% 1.31/0.55    inference(unit_resulting_resolution,[],[f162,f55,f58])).
% 1.31/0.55  fof(f58,plain,(
% 1.31/0.55    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | r2_hidden(sK3(X0,X1),X0)) )),
% 1.31/0.55    inference(definition_unfolding,[],[f36,f54])).
% 1.31/0.55  fof(f54,plain,(
% 1.31/0.55    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.31/0.55    inference(definition_unfolding,[],[f28,f53])).
% 1.31/0.55  fof(f53,plain,(
% 1.31/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.31/0.55    inference(definition_unfolding,[],[f30,f38])).
% 1.31/0.55  fof(f38,plain,(
% 1.31/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f4])).
% 1.31/0.55  fof(f4,axiom,(
% 1.31/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.31/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.31/0.55  fof(f30,plain,(
% 1.31/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f3])).
% 1.31/0.55  fof(f3,axiom,(
% 1.31/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.31/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.31/0.55  fof(f28,plain,(
% 1.31/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f2])).
% 1.31/0.55  fof(f2,axiom,(
% 1.31/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.31/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.31/0.55  fof(f36,plain,(
% 1.31/0.55    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | r2_hidden(sK3(X0,X1),X0)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f19])).
% 1.31/0.55  fof(f19,plain,(
% 1.31/0.55    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 1.31/0.55    inference(ennf_transformation,[],[f5])).
% 1.31/0.55  fof(f5,axiom,(
% 1.31/0.55    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.31/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 1.31/0.55  fof(f55,plain,(
% 1.31/0.55    k11_relat_1(sK1,sK0) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 1.31/0.55    inference(definition_unfolding,[],[f27,f54])).
% 1.31/0.55  fof(f27,plain,(
% 1.31/0.55    k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0))),
% 1.31/0.55    inference(cnf_transformation,[],[f15])).
% 1.31/0.55  fof(f15,plain,(
% 1.31/0.55    ? [X0,X1] : (k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.31/0.55    inference(flattening,[],[f14])).
% 1.31/0.55  fof(f14,plain,(
% 1.31/0.55    ? [X0,X1] : ((k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.31/0.55    inference(ennf_transformation,[],[f12])).
% 1.31/0.55  fof(f12,negated_conjecture,(
% 1.31/0.55    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.31/0.55    inference(negated_conjecture,[],[f11])).
% 1.31/0.55  fof(f11,conjecture,(
% 1.31/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.31/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).
% 1.31/0.55  fof(f162,plain,(
% 1.31/0.55    k1_xboole_0 != k11_relat_1(sK1,sK0)),
% 1.31/0.55    inference(superposition,[],[f144,f103])).
% 1.31/0.55  fof(f103,plain,(
% 1.31/0.55    ( ! [X0] : (k11_relat_1(sK1,X0) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X0))) )),
% 1.31/0.55    inference(unit_resulting_resolution,[],[f24,f56])).
% 1.31/0.55  fof(f56,plain,(
% 1.31/0.55    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 1.31/0.55    inference(definition_unfolding,[],[f29,f54])).
% 1.31/0.55  fof(f29,plain,(
% 1.31/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 1.31/0.55    inference(cnf_transformation,[],[f16])).
% 1.31/0.55  fof(f16,plain,(
% 1.31/0.55    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.31/0.55    inference(ennf_transformation,[],[f7])).
% 1.31/0.55  fof(f7,axiom,(
% 1.31/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.31/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 1.31/0.55  fof(f24,plain,(
% 1.31/0.55    v1_relat_1(sK1)),
% 1.31/0.55    inference(cnf_transformation,[],[f15])).
% 1.31/0.55  fof(f144,plain,(
% 1.31/0.55    ( ! [X2,X0,X1] : (k1_xboole_0 != k9_relat_1(sK1,k2_enumset1(X0,X1,X2,sK0))) )),
% 1.31/0.55    inference(unit_resulting_resolution,[],[f24,f130,f35])).
% 1.31/0.55  fof(f35,plain,(
% 1.31/0.55    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f18])).
% 1.31/0.55  fof(f18,plain,(
% 1.31/0.55    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.31/0.55    inference(ennf_transformation,[],[f8])).
% 1.31/0.55  fof(f8,axiom,(
% 1.31/0.55    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.31/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).
% 1.31/0.55  fof(f130,plain,(
% 1.31/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(k1_relat_1(sK1),k2_enumset1(X0,X1,X2,sK0))) )),
% 1.31/0.55    inference(unit_resulting_resolution,[],[f26,f115,f31])).
% 1.31/0.55  fof(f31,plain,(
% 1.31/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f17])).
% 1.31/0.55  fof(f17,plain,(
% 1.31/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.31/0.55    inference(ennf_transformation,[],[f13])).
% 1.31/0.55  fof(f13,plain,(
% 1.31/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.31/0.55    inference(rectify,[],[f1])).
% 1.31/0.55  fof(f1,axiom,(
% 1.31/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.31/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.31/0.55  fof(f115,plain,(
% 1.31/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k2_enumset1(X1,X2,X3,X0))) )),
% 1.31/0.55    inference(unit_resulting_resolution,[],[f62,f61])).
% 1.31/0.55  fof(f61,plain,(
% 1.31/0.55    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,k2_enumset1(X0,X1,X2,X3)) | ~sP5(X5,X3,X2,X1,X0)) )),
% 1.31/0.55    inference(equality_resolution,[],[f49])).
% 1.31/0.55  fof(f49,plain,(
% 1.31/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~sP5(X5,X3,X2,X1,X0) | r2_hidden(X5,X4) | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 1.31/0.55    inference(cnf_transformation,[],[f23])).
% 1.31/0.55  fof(f23,plain,(
% 1.31/0.55    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 1.31/0.55    inference(ennf_transformation,[],[f6])).
% 1.31/0.55  fof(f6,axiom,(
% 1.31/0.55    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> ~(X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)))),
% 1.31/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).
% 1.31/0.55  fof(f62,plain,(
% 1.31/0.55    ( ! [X2,X0,X5,X1] : (sP5(X5,X5,X2,X1,X0)) )),
% 1.31/0.55    inference(equality_resolution,[],[f47])).
% 1.31/0.55  fof(f47,plain,(
% 1.31/0.55    ( ! [X2,X0,X5,X3,X1] : (X3 != X5 | sP5(X5,X3,X2,X1,X0)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f23])).
% 1.31/0.55  fof(f26,plain,(
% 1.31/0.55    r2_hidden(sK0,k1_relat_1(sK1))),
% 1.31/0.55    inference(cnf_transformation,[],[f15])).
% 1.31/0.55  fof(f186,plain,(
% 1.31/0.55    ~r2_hidden(sK3(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0)),k11_relat_1(sK1,sK0))),
% 1.31/0.55    inference(unit_resulting_resolution,[],[f24,f185,f39])).
% 1.31/0.55  fof(f39,plain,(
% 1.31/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f20])).
% 1.31/0.55  fof(f20,plain,(
% 1.31/0.55    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 1.31/0.55    inference(ennf_transformation,[],[f9])).
% 1.31/0.55  fof(f9,axiom,(
% 1.31/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 1.31/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).
% 1.31/0.55  fof(f185,plain,(
% 1.31/0.55    ~r2_hidden(k4_tarski(sK0,sK3(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0))),sK1)),
% 1.31/0.55    inference(unit_resulting_resolution,[],[f24,f25,f175,f42])).
% 1.31/0.55  fof(f42,plain,(
% 1.31/0.55    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f22])).
% 1.31/0.55  fof(f22,plain,(
% 1.31/0.55    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.31/0.55    inference(flattening,[],[f21])).
% 1.31/0.55  fof(f21,plain,(
% 1.31/0.55    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.31/0.55    inference(ennf_transformation,[],[f10])).
% 1.31/0.55  fof(f10,axiom,(
% 1.31/0.55    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.31/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.31/0.55  fof(f175,plain,(
% 1.31/0.55    k1_funct_1(sK1,sK0) != sK3(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 1.31/0.55    inference(unit_resulting_resolution,[],[f162,f55,f57])).
% 1.31/0.55  fof(f57,plain,(
% 1.31/0.55    ( ! [X0,X1] : (sK3(X0,X1) != X1 | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 1.31/0.55    inference(definition_unfolding,[],[f37,f54])).
% 1.31/0.55  fof(f37,plain,(
% 1.31/0.55    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | sK3(X0,X1) != X1) )),
% 1.31/0.55    inference(cnf_transformation,[],[f19])).
% 1.31/0.55  fof(f25,plain,(
% 1.31/0.55    v1_funct_1(sK1)),
% 1.31/0.55    inference(cnf_transformation,[],[f15])).
% 1.31/0.55  % SZS output end Proof for theBenchmark
% 1.31/0.55  % (362)------------------------------
% 1.31/0.55  % (362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (362)Termination reason: Refutation
% 1.31/0.55  
% 1.31/0.55  % (362)Memory used [KB]: 6396
% 1.31/0.55  % (362)Time elapsed: 0.088 s
% 1.31/0.55  % (362)------------------------------
% 1.31/0.55  % (362)------------------------------
% 1.31/0.55  % (337)Success in time 0.186 s
%------------------------------------------------------------------------------
