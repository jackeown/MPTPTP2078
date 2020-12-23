%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:59 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 107 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :   16
%              Number of atoms          :  153 ( 307 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (12385)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% (12395)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% (12411)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% (12401)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% (12404)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% (12395)Refutation not found, incomplete strategy% (12395)------------------------------
% (12395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12395)Termination reason: Refutation not found, incomplete strategy

% (12395)Memory used [KB]: 10746
% (12395)Time elapsed: 0.136 s
% (12395)------------------------------
% (12395)------------------------------
% (12388)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% (12406)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
fof(f132,plain,(
    $false ),
    inference(resolution,[],[f130,f49])).

fof(f49,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f130,plain,(
    ~ r1_tarski(sK2,sK2) ),
    inference(resolution,[],[f122,f43])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f122,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),sK0)
    | ~ r1_tarski(sK2,sK2) ),
    inference(resolution,[],[f121,f34])).

fof(f34,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).

fof(f121,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(sK2,sK2)
    | ~ r1_tarski(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),sK0) ),
    inference(resolution,[],[f117,f54])).

fof(f54,plain,(
    ! [X6,X7,X5] :
      ( r1_tarski(k9_relat_1(sK2,X5),k9_relat_1(X7,X6))
      | ~ r1_tarski(sK2,X7)
      | ~ v1_relat_1(X7)
      | ~ r1_tarski(X5,X6) ) ),
    inference(resolution,[],[f34,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X3)
      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

fof(f117,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f110,f66])).

fof(f66,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1)
    | ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f36,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f36,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f110,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,k10_relat_1(sK2,X1))),X1) ),
    inference(resolution,[],[f109,f51])).

fof(f51,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(resolution,[],[f34,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f109,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(k7_relat_1(sK2,X4))
      | r1_tarski(k9_relat_1(sK2,k3_xboole_0(X4,k10_relat_1(sK2,X5))),X5) ) ),
    inference(forward_demodulation,[],[f108,f84])).

% (12412)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% (12392)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f84,plain,(
    ! [X6,X5] : k9_relat_1(k7_relat_1(sK2,X5),k3_xboole_0(X5,X6)) = k9_relat_1(sK2,k3_xboole_0(X5,X6)) ),
    inference(resolution,[],[f53,f43])).

fof(f53,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,X4)
      | k9_relat_1(k7_relat_1(sK2,X4),X3) = k9_relat_1(sK2,X3) ) ),
    inference(resolution,[],[f34,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,X2)
      | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f108,plain,(
    ! [X4,X5] :
      ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X4),k3_xboole_0(X4,k10_relat_1(sK2,X5))),X5)
      | ~ v1_relat_1(k7_relat_1(sK2,X4)) ) ),
    inference(forward_demodulation,[],[f65,f52])).

fof(f52,plain,(
    ! [X2,X1] : k10_relat_1(k7_relat_1(sK2,X1),X2) = k3_xboole_0(X1,k10_relat_1(sK2,X2)) ),
    inference(resolution,[],[f34,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f65,plain,(
    ! [X4,X5] :
      ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X4),k10_relat_1(k7_relat_1(sK2,X4),X5)),X5)
      | ~ v1_relat_1(k7_relat_1(sK2,X4)) ) ),
    inference(resolution,[],[f62,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f62,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK2,X0)) ),
    inference(resolution,[],[f56,f34])).

fof(f56,plain,(
    ! [X1] :
      ( ~ v1_relat_1(sK2)
      | v1_funct_1(k7_relat_1(sK2,X1)) ) ),
    inference(resolution,[],[f35,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

% (12398)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:16:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.12/0.51  % (12387)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.12/0.52  % (12399)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.12/0.52  % (12407)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.12/0.52  % (12389)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.12/0.52  % (12396)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.12/0.53  % (12391)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.12/0.54  % (12402)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.12/0.54  % (12414)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.12/0.54  % (12386)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.12/0.54  % (12390)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.37/0.54  % (12397)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.37/0.54  % (12386)Refutation found. Thanks to Tanya!
% 1.37/0.54  % SZS status Theorem for theBenchmark
% 1.37/0.54  % SZS output start Proof for theBenchmark
% 1.37/0.54  % (12385)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.37/0.54  % (12395)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.37/0.54  % (12411)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.37/0.54  % (12401)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.37/0.54  % (12404)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.37/0.54  % (12395)Refutation not found, incomplete strategy% (12395)------------------------------
% 1.37/0.54  % (12395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (12395)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (12395)Memory used [KB]: 10746
% 1.37/0.54  % (12395)Time elapsed: 0.136 s
% 1.37/0.54  % (12395)------------------------------
% 1.37/0.54  % (12395)------------------------------
% 1.37/0.55  % (12388)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.37/0.55  % (12406)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.37/0.55  fof(f132,plain,(
% 1.37/0.55    $false),
% 1.37/0.55    inference(resolution,[],[f130,f49])).
% 1.37/0.55  fof(f49,plain,(
% 1.37/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.37/0.55    inference(equality_resolution,[],[f38])).
% 1.37/0.55  fof(f38,plain,(
% 1.37/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.37/0.55    inference(cnf_transformation,[],[f33])).
% 1.37/0.55  fof(f33,plain,(
% 1.37/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.37/0.55    inference(flattening,[],[f32])).
% 1.37/0.55  fof(f32,plain,(
% 1.37/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.37/0.55    inference(nnf_transformation,[],[f1])).
% 1.37/0.55  fof(f1,axiom,(
% 1.37/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.37/0.55  fof(f130,plain,(
% 1.37/0.55    ~r1_tarski(sK2,sK2)),
% 1.37/0.55    inference(resolution,[],[f122,f43])).
% 1.37/0.55  fof(f43,plain,(
% 1.37/0.55    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f2])).
% 1.37/0.55  fof(f2,axiom,(
% 1.37/0.55    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.37/0.55  fof(f122,plain,(
% 1.37/0.55    ~r1_tarski(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),sK0) | ~r1_tarski(sK2,sK2)),
% 1.37/0.55    inference(resolution,[],[f121,f34])).
% 1.37/0.55  fof(f34,plain,(
% 1.37/0.55    v1_relat_1(sK2)),
% 1.37/0.55    inference(cnf_transformation,[],[f31])).
% 1.37/0.55  fof(f31,plain,(
% 1.37/0.55    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.37/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f30])).
% 1.37/0.55  fof(f30,plain,(
% 1.37/0.55    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.37/0.55    introduced(choice_axiom,[])).
% 1.37/0.55  fof(f18,plain,(
% 1.37/0.55    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.37/0.55    inference(flattening,[],[f17])).
% 1.37/0.55  fof(f17,plain,(
% 1.37/0.55    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.37/0.55    inference(ennf_transformation,[],[f16])).
% 1.37/0.55  fof(f16,negated_conjecture,(
% 1.37/0.55    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 1.37/0.55    inference(negated_conjecture,[],[f15])).
% 1.37/0.55  fof(f15,conjecture,(
% 1.37/0.55    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).
% 1.37/0.55  fof(f121,plain,(
% 1.37/0.55    ~v1_relat_1(sK2) | ~r1_tarski(sK2,sK2) | ~r1_tarski(k3_xboole_0(sK0,k10_relat_1(sK2,sK1)),sK0)),
% 1.37/0.55    inference(resolution,[],[f117,f54])).
% 1.37/0.55  fof(f54,plain,(
% 1.37/0.55    ( ! [X6,X7,X5] : (r1_tarski(k9_relat_1(sK2,X5),k9_relat_1(X7,X6)) | ~r1_tarski(sK2,X7) | ~v1_relat_1(X7) | ~r1_tarski(X5,X6)) )),
% 1.37/0.55    inference(resolution,[],[f34,f40])).
% 1.37/0.55  fof(f40,plain,(
% 1.37/0.55    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3) | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))) )),
% 1.37/0.55    inference(cnf_transformation,[],[f20])).
% 1.37/0.55  fof(f20,plain,(
% 1.37/0.55    ! [X0,X1,X2] : (! [X3] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 1.37/0.55    inference(flattening,[],[f19])).
% 1.37/0.55  fof(f19,plain,(
% 1.37/0.55    ! [X0,X1,X2] : (! [X3] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | (~r1_tarski(X0,X1) | ~r1_tarski(X2,X3))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 1.37/0.55    inference(ennf_transformation,[],[f10])).
% 1.37/0.55  fof(f10,axiom,(
% 1.37/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).
% 1.37/0.55  fof(f117,plain,(
% 1.37/0.55    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0))),
% 1.37/0.55    inference(resolution,[],[f110,f66])).
% 1.37/0.55  fof(f66,plain,(
% 1.37/0.55    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1) | ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0))),
% 1.37/0.55    inference(resolution,[],[f36,f42])).
% 1.37/0.55  fof(f42,plain,(
% 1.37/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f23])).
% 1.37/0.55  fof(f23,plain,(
% 1.37/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.37/0.55    inference(flattening,[],[f22])).
% 1.37/0.55  fof(f22,plain,(
% 1.37/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.37/0.55    inference(ennf_transformation,[],[f3])).
% 1.37/0.55  fof(f3,axiom,(
% 1.37/0.55    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.37/0.55  fof(f36,plain,(
% 1.37/0.55    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))),
% 1.37/0.55    inference(cnf_transformation,[],[f31])).
% 1.37/0.55  fof(f110,plain,(
% 1.37/0.55    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,k10_relat_1(sK2,X1))),X1)) )),
% 1.37/0.55    inference(resolution,[],[f109,f51])).
% 1.37/0.55  fof(f51,plain,(
% 1.37/0.55    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) )),
% 1.37/0.55    inference(resolution,[],[f34,f48])).
% 1.37/0.55  fof(f48,plain,(
% 1.37/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 1.37/0.55    inference(cnf_transformation,[],[f29])).
% 1.37/0.55  fof(f29,plain,(
% 1.37/0.55    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.37/0.55    inference(ennf_transformation,[],[f9])).
% 1.37/0.55  fof(f9,axiom,(
% 1.37/0.55    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.37/0.55  fof(f109,plain,(
% 1.37/0.55    ( ! [X4,X5] : (~v1_relat_1(k7_relat_1(sK2,X4)) | r1_tarski(k9_relat_1(sK2,k3_xboole_0(X4,k10_relat_1(sK2,X5))),X5)) )),
% 1.37/0.55    inference(forward_demodulation,[],[f108,f84])).
% 1.37/0.55  % (12412)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.37/0.55  % (12392)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.37/0.55  fof(f84,plain,(
% 1.37/0.55    ( ! [X6,X5] : (k9_relat_1(k7_relat_1(sK2,X5),k3_xboole_0(X5,X6)) = k9_relat_1(sK2,k3_xboole_0(X5,X6))) )),
% 1.37/0.55    inference(resolution,[],[f53,f43])).
% 1.37/0.55  fof(f53,plain,(
% 1.37/0.55    ( ! [X4,X3] : (~r1_tarski(X3,X4) | k9_relat_1(k7_relat_1(sK2,X4),X3) = k9_relat_1(sK2,X3)) )),
% 1.37/0.55    inference(resolution,[],[f34,f41])).
% 1.37/0.55  fof(f41,plain,(
% 1.37/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X1,X2) | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f21])).
% 1.37/0.55  fof(f21,plain,(
% 1.37/0.55    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 1.37/0.55    inference(ennf_transformation,[],[f11])).
% 1.37/0.55  fof(f11,axiom,(
% 1.37/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 1.37/0.55  fof(f108,plain,(
% 1.37/0.55    ( ! [X4,X5] : (r1_tarski(k9_relat_1(k7_relat_1(sK2,X4),k3_xboole_0(X4,k10_relat_1(sK2,X5))),X5) | ~v1_relat_1(k7_relat_1(sK2,X4))) )),
% 1.37/0.55    inference(forward_demodulation,[],[f65,f52])).
% 1.37/0.55  fof(f52,plain,(
% 1.37/0.55    ( ! [X2,X1] : (k10_relat_1(k7_relat_1(sK2,X1),X2) = k3_xboole_0(X1,k10_relat_1(sK2,X2))) )),
% 1.37/0.55    inference(resolution,[],[f34,f44])).
% 1.37/0.55  fof(f44,plain,(
% 1.37/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 1.37/0.55    inference(cnf_transformation,[],[f24])).
% 1.37/0.55  fof(f24,plain,(
% 1.37/0.55    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.37/0.55    inference(ennf_transformation,[],[f13])).
% 1.37/0.55  fof(f13,axiom,(
% 1.37/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 1.37/0.55  fof(f65,plain,(
% 1.37/0.55    ( ! [X4,X5] : (r1_tarski(k9_relat_1(k7_relat_1(sK2,X4),k10_relat_1(k7_relat_1(sK2,X4),X5)),X5) | ~v1_relat_1(k7_relat_1(sK2,X4))) )),
% 1.37/0.55    inference(resolution,[],[f62,f45])).
% 1.37/0.55  fof(f45,plain,(
% 1.37/0.55    ( ! [X0,X1] : (~v1_funct_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f26])).
% 1.37/0.55  fof(f26,plain,(
% 1.37/0.55    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.37/0.55    inference(flattening,[],[f25])).
% 1.37/0.55  fof(f25,plain,(
% 1.37/0.55    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.37/0.55    inference(ennf_transformation,[],[f14])).
% 1.37/0.55  fof(f14,axiom,(
% 1.37/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 1.37/0.55  fof(f62,plain,(
% 1.37/0.55    ( ! [X0] : (v1_funct_1(k7_relat_1(sK2,X0))) )),
% 1.37/0.55    inference(resolution,[],[f56,f34])).
% 1.37/0.55  fof(f56,plain,(
% 1.37/0.55    ( ! [X1] : (~v1_relat_1(sK2) | v1_funct_1(k7_relat_1(sK2,X1))) )),
% 1.37/0.55    inference(resolution,[],[f35,f47])).
% 1.37/0.55  fof(f47,plain,(
% 1.37/0.55    ( ! [X0,X1] : (~v1_funct_1(X0) | v1_funct_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f28])).
% 1.37/0.55  fof(f28,plain,(
% 1.37/0.55    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.37/0.55    inference(flattening,[],[f27])).
% 1.37/0.55  fof(f27,plain,(
% 1.37/0.55    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.37/0.55    inference(ennf_transformation,[],[f12])).
% 1.37/0.55  % (12398)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.37/0.55  fof(f12,axiom,(
% 1.37/0.55    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 1.37/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).
% 1.37/0.55  fof(f35,plain,(
% 1.37/0.55    v1_funct_1(sK2)),
% 1.37/0.55    inference(cnf_transformation,[],[f31])).
% 1.37/0.55  % SZS output end Proof for theBenchmark
% 1.37/0.55  % (12386)------------------------------
% 1.37/0.55  % (12386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (12386)Termination reason: Refutation
% 1.37/0.55  
% 1.37/0.55  % (12386)Memory used [KB]: 1791
% 1.37/0.55  % (12386)Time elapsed: 0.129 s
% 1.37/0.55  % (12386)------------------------------
% 1.37/0.55  % (12386)------------------------------
% 1.37/0.55  % (12410)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.37/0.55  % (12393)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.37/0.55  % (12384)Success in time 0.187 s
%------------------------------------------------------------------------------
