%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.32s
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
fof(f324,plain,(
    $false ),
    inference(resolution,[],[f309,f59])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
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

fof(f309,plain,(
    ~ r1_tarski(sK0,sK0) ),
    inference(backward_demodulation,[],[f200,f306])).

fof(f306,plain,(
    sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f285,f84])).

fof(f84,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0) ),
    inference(unit_resulting_resolution,[],[f42,f41,f44,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f44,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f41,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f285,plain,(
    sK0 = k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f283,f83])).

fof(f83,plain,(
    ! [X0] : k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0) ),
    inference(unit_resulting_resolution,[],[f42,f41,f44,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(f283,plain,(
    sK0 = k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),sK0)) ),
    inference(unit_resulting_resolution,[],[f72,f73,f274,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f274,plain,(
    r1_tarski(sK0,k2_relat_1(k2_funct_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f42,f41,f44,f43,f102,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

fof(f102,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,k2_relat_1(k2_funct_1(sK1)))) ),
    inference(forward_demodulation,[],[f101,f83])).

fof(f101,plain,(
    ! [X0] : r1_tarski(k10_relat_1(k2_funct_1(sK1),X0),k9_relat_1(sK1,k2_relat_1(k2_funct_1(sK1)))) ),
    inference(forward_demodulation,[],[f96,f83])).

fof(f96,plain,(
    ! [X0] : r1_tarski(k10_relat_1(k2_funct_1(sK1),X0),k10_relat_1(k2_funct_1(sK1),k2_relat_1(k2_funct_1(sK1)))) ),
    inference(unit_resulting_resolution,[],[f72,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).

fof(f43,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    v1_funct_1(k2_funct_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f41,f42,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f72,plain,(
    v1_relat_1(k2_funct_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f41,f42,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f200,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f45,f126,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f126,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f41,f43,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f45,plain,(
    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:34:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (26357)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.49  % (26357)Refutation not found, incomplete strategy% (26357)------------------------------
% 0.20/0.49  % (26357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (26357)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (26357)Memory used [KB]: 10746
% 0.20/0.50  % (26357)Time elapsed: 0.090 s
% 0.20/0.50  % (26357)------------------------------
% 0.20/0.50  % (26357)------------------------------
% 0.20/0.51  % (26364)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.51  % (26349)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (26359)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.51  % (26352)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (26348)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (26367)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.52  % (26372)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.52  % (26358)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.53  % (26372)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (26368)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (26369)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (26361)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (26360)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (26353)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.32/0.54  % (26356)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.32/0.54  % (26365)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.32/0.54  % (26375)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.32/0.54  % (26350)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.32/0.54  % (26347)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.32/0.54  % (26347)Refutation not found, incomplete strategy% (26347)------------------------------
% 1.32/0.54  % (26347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (26347)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (26347)Memory used [KB]: 1663
% 1.32/0.54  % (26347)Time elapsed: 0.126 s
% 1.32/0.54  % (26347)------------------------------
% 1.32/0.54  % (26347)------------------------------
% 1.32/0.55  % SZS output start Proof for theBenchmark
% 1.32/0.55  fof(f324,plain,(
% 1.32/0.55    $false),
% 1.32/0.55    inference(resolution,[],[f309,f59])).
% 1.32/0.55  fof(f59,plain,(
% 1.32/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.32/0.55    inference(equality_resolution,[],[f47])).
% 1.32/0.55  fof(f47,plain,(
% 1.32/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.32/0.55    inference(cnf_transformation,[],[f2])).
% 1.32/0.55  fof(f2,axiom,(
% 1.32/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.32/0.55  fof(f309,plain,(
% 1.32/0.55    ~r1_tarski(sK0,sK0)),
% 1.32/0.55    inference(backward_demodulation,[],[f200,f306])).
% 1.32/0.55  fof(f306,plain,(
% 1.32/0.55    sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 1.32/0.55    inference(superposition,[],[f285,f84])).
% 1.32/0.55  fof(f84,plain,(
% 1.32/0.55    ( ! [X0] : (k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0)) )),
% 1.32/0.55    inference(unit_resulting_resolution,[],[f42,f41,f44,f53])).
% 1.32/0.55  fof(f53,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f34])).
% 1.32/0.55  fof(f34,plain,(
% 1.32/0.55    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.32/0.55    inference(flattening,[],[f33])).
% 1.32/0.55  fof(f33,plain,(
% 1.32/0.55    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.32/0.55    inference(ennf_transformation,[],[f20])).
% 1.32/0.55  fof(f20,axiom,(
% 1.32/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 1.32/0.55  fof(f44,plain,(
% 1.32/0.55    v2_funct_1(sK1)),
% 1.32/0.55    inference(cnf_transformation,[],[f25])).
% 1.32/0.55  fof(f25,plain,(
% 1.32/0.55    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.32/0.55    inference(flattening,[],[f24])).
% 1.32/0.55  fof(f24,plain,(
% 1.32/0.55    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.32/0.55    inference(ennf_transformation,[],[f23])).
% 1.32/0.55  fof(f23,negated_conjecture,(
% 1.32/0.55    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 1.32/0.55    inference(negated_conjecture,[],[f22])).
% 1.32/0.55  fof(f22,conjecture,(
% 1.32/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 1.32/0.55  fof(f41,plain,(
% 1.32/0.55    v1_relat_1(sK1)),
% 1.32/0.55    inference(cnf_transformation,[],[f25])).
% 1.32/0.55  fof(f42,plain,(
% 1.32/0.55    v1_funct_1(sK1)),
% 1.32/0.55    inference(cnf_transformation,[],[f25])).
% 1.32/0.55  fof(f285,plain,(
% 1.32/0.55    sK0 = k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,sK0))),
% 1.32/0.55    inference(forward_demodulation,[],[f283,f83])).
% 1.32/0.55  fof(f83,plain,(
% 1.32/0.55    ( ! [X0] : (k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0)) )),
% 1.32/0.55    inference(unit_resulting_resolution,[],[f42,f41,f44,f54])).
% 1.32/0.55  fof(f54,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f36])).
% 1.32/0.55  fof(f36,plain,(
% 1.32/0.55    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.32/0.55    inference(flattening,[],[f35])).
% 1.32/0.55  fof(f35,plain,(
% 1.32/0.55    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.32/0.55    inference(ennf_transformation,[],[f19])).
% 1.32/0.55  fof(f19,axiom,(
% 1.32/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
% 1.32/0.55  fof(f283,plain,(
% 1.32/0.55    sK0 = k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),sK0))),
% 1.32/0.55    inference(unit_resulting_resolution,[],[f72,f73,f274,f52])).
% 1.32/0.55  fof(f52,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0) )),
% 1.32/0.55    inference(cnf_transformation,[],[f32])).
% 1.32/0.55  fof(f32,plain,(
% 1.32/0.55    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.32/0.55    inference(flattening,[],[f31])).
% 1.32/0.55  fof(f31,plain,(
% 1.32/0.55    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.32/0.55    inference(ennf_transformation,[],[f18])).
% 1.32/0.55  fof(f18,axiom,(
% 1.32/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 1.32/0.55  fof(f274,plain,(
% 1.32/0.55    r1_tarski(sK0,k2_relat_1(k2_funct_1(sK1)))),
% 1.32/0.55    inference(unit_resulting_resolution,[],[f42,f41,f44,f43,f102,f51])).
% 1.32/0.55  fof(f51,plain,(
% 1.32/0.55    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_1(X2) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_relat_1(X2) | r1_tarski(X0,X1)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f30])).
% 1.32/0.55  fof(f30,plain,(
% 1.32/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.32/0.55    inference(flattening,[],[f29])).
% 1.32/0.55  fof(f29,plain,(
% 1.32/0.55    ! [X0,X1,X2] : ((r1_tarski(X0,X1) | (~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.32/0.55    inference(ennf_transformation,[],[f21])).
% 1.32/0.55  fof(f21,axiom,(
% 1.32/0.55    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).
% 1.32/0.55  fof(f102,plain,(
% 1.32/0.55    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,k2_relat_1(k2_funct_1(sK1))))) )),
% 1.32/0.55    inference(forward_demodulation,[],[f101,f83])).
% 1.32/0.55  fof(f101,plain,(
% 1.32/0.55    ( ! [X0] : (r1_tarski(k10_relat_1(k2_funct_1(sK1),X0),k9_relat_1(sK1,k2_relat_1(k2_funct_1(sK1))))) )),
% 1.32/0.55    inference(forward_demodulation,[],[f96,f83])).
% 1.32/0.55  fof(f96,plain,(
% 1.32/0.55    ( ! [X0] : (r1_tarski(k10_relat_1(k2_funct_1(sK1),X0),k10_relat_1(k2_funct_1(sK1),k2_relat_1(k2_funct_1(sK1))))) )),
% 1.32/0.55    inference(unit_resulting_resolution,[],[f72,f56])).
% 1.32/0.55  fof(f56,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))) )),
% 1.32/0.55    inference(cnf_transformation,[],[f38])).
% 1.32/0.55  fof(f38,plain,(
% 1.32/0.55    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.32/0.55    inference(ennf_transformation,[],[f13])).
% 1.32/0.55  fof(f13,axiom,(
% 1.32/0.55    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).
% 1.32/0.55  fof(f43,plain,(
% 1.32/0.55    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.32/0.55    inference(cnf_transformation,[],[f25])).
% 1.32/0.55  fof(f73,plain,(
% 1.32/0.55    v1_funct_1(k2_funct_1(sK1))),
% 1.32/0.55    inference(unit_resulting_resolution,[],[f41,f42,f58])).
% 1.32/0.55  fof(f58,plain,(
% 1.32/0.55    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 1.32/0.55    inference(cnf_transformation,[],[f40])).
% 1.32/0.55  fof(f40,plain,(
% 1.32/0.55    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.32/0.55    inference(flattening,[],[f39])).
% 1.32/0.55  fof(f39,plain,(
% 1.32/0.55    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.32/0.55    inference(ennf_transformation,[],[f15])).
% 1.32/0.55  fof(f15,axiom,(
% 1.32/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.32/0.55  fof(f72,plain,(
% 1.32/0.55    v1_relat_1(k2_funct_1(sK1))),
% 1.32/0.55    inference(unit_resulting_resolution,[],[f41,f42,f57])).
% 1.32/0.55  fof(f57,plain,(
% 1.32/0.55    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 1.32/0.55    inference(cnf_transformation,[],[f40])).
% 1.32/0.55  fof(f200,plain,(
% 1.32/0.55    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 1.32/0.55    inference(unit_resulting_resolution,[],[f45,f126,f48])).
% 1.32/0.55  fof(f48,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.32/0.55    inference(cnf_transformation,[],[f2])).
% 1.32/0.55  fof(f126,plain,(
% 1.32/0.55    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.32/0.55    inference(unit_resulting_resolution,[],[f41,f43,f49])).
% 1.32/0.55  fof(f49,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 1.32/0.55    inference(cnf_transformation,[],[f27])).
% 1.32/0.55  fof(f27,plain,(
% 1.32/0.55    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.32/0.55    inference(flattening,[],[f26])).
% 1.32/0.55  fof(f26,plain,(
% 1.32/0.55    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.32/0.55    inference(ennf_transformation,[],[f17])).
% 1.32/0.55  fof(f17,axiom,(
% 1.32/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 1.32/0.55  fof(f45,plain,(
% 1.32/0.55    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 1.32/0.55    inference(cnf_transformation,[],[f25])).
% 1.32/0.55  % SZS output end Proof for theBenchmark
% 1.32/0.55  % (26372)------------------------------
% 1.32/0.55  % (26372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (26372)Termination reason: Refutation
% 1.32/0.55  
% 1.32/0.55  % (26372)Memory used [KB]: 6396
% 1.32/0.55  % (26372)Time elapsed: 0.125 s
% 1.32/0.55  % (26372)------------------------------
% 1.32/0.55  % (26372)------------------------------
% 1.32/0.55  % (26340)Success in time 0.182 s
%------------------------------------------------------------------------------
