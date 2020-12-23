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
% DateTime   : Thu Dec  3 12:53:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 100 expanded)
%              Number of leaves         :   10 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :   86 ( 194 expanded)
%              Number of equality atoms :   27 (  73 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f150,plain,(
    $false ),
    inference(global_subsumption,[],[f141,f145])).

fof(f145,plain,(
    r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f142,f94])).

fof(f94,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_relat_1(sK1))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(global_subsumption,[],[f17,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | ~ v1_relat_1(sK1)
      | r2_hidden(X0,k2_relat_1(sK1)) ) ),
    inference(trivial_inequality_removal,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X0,sK0)
      | ~ v1_relat_1(sK1)
      | r2_hidden(X0,k2_relat_1(sK1)) ) ),
    inference(superposition,[],[f39,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,k3_enumset1(X0,X0,X0,X0,X0))
      | ~ v1_relat_1(X1)
      | r2_hidden(X0,k2_relat_1(X1)) ) ),
    inference(definition_unfolding,[],[f22,f38])).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f20,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f21,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f26,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
      | r2_hidden(X0,k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

fof(f39,plain,(
    ! [X2] :
      ( k1_xboole_0 != k10_relat_1(sK1,k3_enumset1(X2,X2,X2,X2,X2))
      | ~ r2_hidden(X2,sK0) ) ),
    inference(definition_unfolding,[],[f16,f38])).

fof(f16,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | k1_xboole_0 != k10_relat_1(sK1,k1_tarski(X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      & ! [X2] :
          ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2))
          | ~ r2_hidden(X2,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      & ! [X2] :
          ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2))
          | ~ r2_hidden(X2,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( ! [X2] :
              ~ ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
                & r2_hidden(X2,X0) )
         => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ~ ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
              & r2_hidden(X2,X0) )
       => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_funct_1)).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f142,plain,(
    r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),sK0) ),
    inference(unit_resulting_resolution,[],[f95,f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f95,plain,(
    sP3(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k2_relat_1(sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f45,f57,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( sP3(sK2(X0,X1,X2),X1,X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f57,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f19,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f34,f37])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f19,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f45,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f18,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f18,plain,(
    ~ r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f141,plain,(
    ~ r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f95,f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:51:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (2040)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (2039)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (2048)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (2058)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (2047)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (2046)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (2036)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (2037)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (2050)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (2059)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (2053)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (2054)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (2059)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (2041)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (2056)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (2042)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(global_subsumption,[],[f141,f145])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k2_relat_1(sK1))),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f142,f94])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK1)) | ~r2_hidden(X0,sK0)) )),
% 0.21/0.52    inference(global_subsumption,[],[f17,f93])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,sK0) | ~v1_relat_1(sK1) | r2_hidden(X0,k2_relat_1(sK1))) )),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f90])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(X0,sK0) | ~v1_relat_1(sK1) | r2_hidden(X0,k2_relat_1(sK1))) )),
% 0.21/0.52    inference(superposition,[],[f39,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,k3_enumset1(X0,X0,X0,X0,X0)) | ~v1_relat_1(X1) | r2_hidden(X0,k2_relat_1(X1))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f22,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f20,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f21,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f26,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X2] : (k1_xboole_0 != k10_relat_1(sK1,k3_enumset1(X2,X2,X2,X2,X2)) | ~r2_hidden(X2,sK0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f16,f38])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(X2,sK0) | k1_xboole_0 != k10_relat_1(sK1,k1_tarski(X2))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) & ! [X2] : (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2)) | ~r2_hidden(X2,X0)) & v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0,X1] : ((~r1_tarski(X0,k2_relat_1(X1)) & ! [X2] : (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2)) | ~r2_hidden(X2,X0))) & v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (v1_relat_1(X1) => (! [X2] : ~(k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2)) & r2_hidden(X2,X0)) => r1_tarski(X0,k2_relat_1(X1))))),
% 0.21/0.52    inference(negated_conjecture,[],[f10])).
% 0.21/0.52  fof(f10,conjecture,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (! [X2] : ~(k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2)) & r2_hidden(X2,X0)) => r1_tarski(X0,k2_relat_1(X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_funct_1)).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    v1_relat_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),sK0)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f95,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    sP3(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k2_relat_1(sK1),sK0)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f45,f57,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (sP3(sK2(X0,X1,X2),X1,X0) | r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f19,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f34,f37])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    k1_xboole_0 != k4_xboole_0(sK0,k2_relat_1(sK1))),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f18,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ~r1_tarski(sK0,k2_relat_1(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    ~r2_hidden(sK2(sK0,k2_relat_1(sK1),k1_xboole_0),k2_relat_1(sK1))),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f95,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~sP3(X3,X1,X0) | ~r2_hidden(X3,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (2059)------------------------------
% 0.21/0.52  % (2059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2059)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (2059)Memory used [KB]: 6268
% 0.21/0.52  % (2059)Time elapsed: 0.085 s
% 0.21/0.52  % (2059)------------------------------
% 0.21/0.52  % (2059)------------------------------
% 0.21/0.53  % (2031)Success in time 0.169 s
%------------------------------------------------------------------------------
