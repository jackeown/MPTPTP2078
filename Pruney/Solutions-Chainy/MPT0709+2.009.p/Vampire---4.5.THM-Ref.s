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
% DateTime   : Thu Dec  3 12:54:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 191 expanded)
%              Number of leaves         :    9 (  38 expanded)
%              Depth                    :   14
%              Number of atoms          :  157 ( 722 expanded)
%              Number of equality atoms :   25 ( 132 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f325,plain,(
    $false ),
    inference(resolution,[],[f310,f60])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f310,plain,(
    ~ r1_tarski(sK0,sK0) ),
    inference(backward_demodulation,[],[f201,f307])).

fof(f307,plain,(
    sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f286,f85])).

fof(f85,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0) ),
    inference(unit_resulting_resolution,[],[f43,f42,f45,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f45,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f42,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f43,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f286,plain,(
    sK0 = k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f284,f84])).

fof(f84,plain,(
    ! [X0] : k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0) ),
    inference(unit_resulting_resolution,[],[f43,f42,f45,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(f284,plain,(
    sK0 = k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),sK0)) ),
    inference(unit_resulting_resolution,[],[f73,f74,f275,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f275,plain,(
    r1_tarski(sK0,k2_relat_1(k2_funct_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f43,f42,f45,f44,f103,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

fof(f103,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,k2_relat_1(k2_funct_1(sK1)))) ),
    inference(forward_demodulation,[],[f102,f84])).

fof(f102,plain,(
    ! [X0] : r1_tarski(k10_relat_1(k2_funct_1(sK1),X0),k9_relat_1(sK1,k2_relat_1(k2_funct_1(sK1)))) ),
    inference(forward_demodulation,[],[f97,f84])).

fof(f97,plain,(
    ! [X0] : r1_tarski(k10_relat_1(k2_funct_1(sK1),X0),k10_relat_1(k2_funct_1(sK1),k2_relat_1(k2_funct_1(sK1)))) ),
    inference(unit_resulting_resolution,[],[f73,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).

fof(f44,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    v1_funct_1(k2_funct_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f42,f43,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f73,plain,(
    v1_relat_1(k2_funct_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f42,f43,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f201,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f46,f127,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f127,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f42,f44,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f46,plain,(
    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:02:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (22576)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.48  % (22581)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.48  % (22568)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.49  % (22568)Refutation not found, incomplete strategy% (22568)------------------------------
% 0.22/0.49  % (22568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (22568)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (22568)Memory used [KB]: 10746
% 0.22/0.49  % (22568)Time elapsed: 0.082 s
% 0.22/0.49  % (22568)------------------------------
% 0.22/0.49  % (22568)------------------------------
% 0.22/0.49  % (22573)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.49  % (22585)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.52  % (22561)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (22577)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.52  % (22566)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (22578)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.53  % (22569)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (22558)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (22570)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (22560)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (22575)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (22586)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (22586)Refutation not found, incomplete strategy% (22586)------------------------------
% 0.22/0.54  % (22586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (22586)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (22586)Memory used [KB]: 10746
% 0.22/0.54  % (22586)Time elapsed: 0.117 s
% 0.22/0.54  % (22586)------------------------------
% 0.22/0.54  % (22586)------------------------------
% 0.22/0.54  % (22562)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (22559)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (22559)Refutation not found, incomplete strategy% (22559)------------------------------
% 0.22/0.54  % (22559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (22559)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (22559)Memory used [KB]: 1663
% 0.22/0.54  % (22559)Time elapsed: 0.124 s
% 0.22/0.54  % (22559)------------------------------
% 0.22/0.54  % (22559)------------------------------
% 0.22/0.54  % (22587)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (22587)Refutation not found, incomplete strategy% (22587)------------------------------
% 0.22/0.55  % (22587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (22587)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (22587)Memory used [KB]: 1663
% 0.22/0.55  % (22587)Time elapsed: 0.129 s
% 0.22/0.55  % (22587)------------------------------
% 0.22/0.55  % (22587)------------------------------
% 0.22/0.55  % (22563)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (22579)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (22639)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 0.22/0.55  % (22582)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (22580)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (22571)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.55  % (22583)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.56  % (22574)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.56  % (22567)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.56  % (22574)Refutation not found, incomplete strategy% (22574)------------------------------
% 0.22/0.56  % (22574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (22574)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (22574)Memory used [KB]: 10618
% 0.22/0.56  % (22574)Time elapsed: 0.138 s
% 0.22/0.56  % (22574)------------------------------
% 0.22/0.56  % (22574)------------------------------
% 0.22/0.56  % (22565)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.56  % (22564)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (22583)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f325,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(resolution,[],[f310,f60])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.56    inference(equality_resolution,[],[f48])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.56  fof(f310,plain,(
% 0.22/0.56    ~r1_tarski(sK0,sK0)),
% 0.22/0.56    inference(backward_demodulation,[],[f201,f307])).
% 0.22/0.56  fof(f307,plain,(
% 0.22/0.56    sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 0.22/0.56    inference(superposition,[],[f286,f85])).
% 0.22/0.56  fof(f85,plain,(
% 0.22/0.56    ( ! [X0] : (k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0)) )),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f43,f42,f45,f54])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(flattening,[],[f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f21])).
% 0.22/0.56  fof(f21,axiom,(
% 0.22/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    v2_funct_1(sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.56    inference(flattening,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f24])).
% 0.22/0.56  fof(f24,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.22/0.56    inference(negated_conjecture,[],[f23])).
% 0.22/0.56  fof(f23,conjecture,(
% 0.22/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    v1_relat_1(sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    v1_funct_1(sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f286,plain,(
% 0.22/0.56    sK0 = k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,sK0))),
% 0.22/0.56    inference(forward_demodulation,[],[f284,f84])).
% 0.22/0.56  fof(f84,plain,(
% 0.22/0.56    ( ! [X0] : (k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0)) )),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f43,f42,f45,f55])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f37])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(flattening,[],[f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,axiom,(
% 0.22/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
% 0.22/0.56  fof(f284,plain,(
% 0.22/0.56    sK0 = k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),sK0))),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f73,f74,f275,f53])).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(flattening,[],[f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f19])).
% 0.22/0.56  fof(f19,axiom,(
% 0.22/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 0.22/0.56  fof(f275,plain,(
% 0.22/0.56    r1_tarski(sK0,k2_relat_1(k2_funct_1(sK1)))),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f43,f42,f45,f44,f103,f52])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_1(X2) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_relat_1(X2) | r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.56    inference(flattening,[],[f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((r1_tarski(X0,X1) | (~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.56    inference(ennf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).
% 0.22/0.56  fof(f103,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,k2_relat_1(k2_funct_1(sK1))))) )),
% 0.22/0.56    inference(forward_demodulation,[],[f102,f84])).
% 0.22/0.56  fof(f102,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k10_relat_1(k2_funct_1(sK1),X0),k9_relat_1(sK1,k2_relat_1(k2_funct_1(sK1))))) )),
% 0.22/0.56    inference(forward_demodulation,[],[f97,f84])).
% 0.22/0.56  fof(f97,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k10_relat_1(k2_funct_1(sK1),X0),k10_relat_1(k2_funct_1(sK1),k2_relat_1(k2_funct_1(sK1))))) )),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f73,f57])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f39])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,axiom,(
% 0.22/0.56    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f74,plain,(
% 0.22/0.56    v1_funct_1(k2_funct_1(sK1))),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f42,f43,f59])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f41])).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(flattening,[],[f40])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,axiom,(
% 0.22/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    v1_relat_1(k2_funct_1(sK1))),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f42,f43,f58])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f41])).
% 0.22/0.56  fof(f201,plain,(
% 0.22/0.56    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f46,f127,f49])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f2])).
% 0.22/0.56  fof(f127,plain,(
% 0.22/0.56    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f42,f44,f50])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(flattening,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,axiom,(
% 0.22/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (22583)------------------------------
% 0.22/0.56  % (22583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (22583)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (22583)Memory used [KB]: 6396
% 0.22/0.56  % (22583)Time elapsed: 0.145 s
% 0.22/0.56  % (22583)------------------------------
% 0.22/0.56  % (22583)------------------------------
% 1.46/0.56  % (22557)Success in time 0.192 s
%------------------------------------------------------------------------------
