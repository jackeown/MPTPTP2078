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
% DateTime   : Thu Dec  3 12:55:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 (  96 expanded)
%              Number of leaves         :    5 (  17 expanded)
%              Depth                    :   12
%              Number of atoms          :  123 ( 362 expanded)
%              Number of equality atoms :   31 (  75 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108,plain,(
    $false ),
    inference(subsumption_resolution,[],[f107,f19])).

fof(f19,plain,(
    sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1
          & r1_tarski(X1,k1_relat_1(X0))
          & v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

% (20882)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% (20877)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1
          & r1_tarski(X1,k1_relat_1(X0))
          & v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( r1_tarski(X1,k1_relat_1(X0))
              & v2_funct_1(X0) )
           => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
         => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).

fof(f107,plain,(
    sK1 = k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f67,f18])).

fof(f18,plain,(
    r1_tarski(sK1,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_relat_1(sK0))
      | k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,X1)) = X1 ) ),
    inference(forward_demodulation,[],[f66,f36])).

fof(f36,plain,(
    ! [X0] : k9_relat_1(sK0,X0) = k10_relat_1(k2_funct_1(sK0),X0) ),
    inference(subsumption_resolution,[],[f35,f21])).

fof(f21,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK0)
      | k9_relat_1(sK0,X0) = k10_relat_1(k2_funct_1(sK0),X0) ) ),
    inference(subsumption_resolution,[],[f30,f20])).

% (20864)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
fof(f20,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK0)
      | ~ v1_funct_1(sK0)
      | k9_relat_1(sK0,X0) = k10_relat_1(k2_funct_1(sK0),X0) ) ),
    inference(resolution,[],[f17,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

fof(f17,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f66,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_relat_1(sK0))
      | k9_relat_1(k2_funct_1(sK0),k10_relat_1(k2_funct_1(sK0),X1)) = X1 ) ),
    inference(forward_demodulation,[],[f65,f34])).

fof(f34,plain,(
    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f33,f21])).

fof(f33,plain,
    ( ~ v1_funct_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f29,f20])).

fof(f29,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f17,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f65,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k2_relat_1(k2_funct_1(sK0)))
      | k9_relat_1(k2_funct_1(sK0),k10_relat_1(k2_funct_1(sK0),X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f57,f44])).

fof(f44,plain,(
    v1_funct_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f38,f21])).

fof(f38,plain,
    ( ~ v1_funct_1(sK0)
    | v1_funct_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f20,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f57,plain,(
    ! [X1] :
      ( ~ v1_funct_1(k2_funct_1(sK0))
      | ~ r1_tarski(X1,k2_relat_1(k2_funct_1(sK0)))
      | k9_relat_1(k2_funct_1(sK0),k10_relat_1(k2_funct_1(sK0),X1)) = X1 ) ),
    inference(resolution,[],[f43,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f43,plain,(
    v1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f37,f21])).

fof(f37,plain,
    ( ~ v1_funct_1(sK0)
    | v1_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f20,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:55:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (20863)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.49  % (20872)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.49  % (20860)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.49  % (20874)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.50  % (20859)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.50  % (20862)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.50  % (20880)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.50  % (20861)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.50  % (20862)Refutation not found, incomplete strategy% (20862)------------------------------
% 0.20/0.50  % (20862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (20862)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (20862)Memory used [KB]: 10490
% 0.20/0.50  % (20862)Time elapsed: 0.091 s
% 0.20/0.50  % (20862)------------------------------
% 0.20/0.50  % (20862)------------------------------
% 0.20/0.50  % (20866)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (20880)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f107,f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1))),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1 & r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f7])).
% 0.20/0.50  % (20882)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.50  % (20877)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.50  fof(f7,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1 & (r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 0.20/0.50    inference(negated_conjecture,[],[f5])).
% 0.20/0.50  fof(f5,conjecture,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    sK1 = k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1))),
% 0.20/0.50    inference(resolution,[],[f67,f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    r1_tarski(sK1,k1_relat_1(sK0))),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK0)) | k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,X1)) = X1) )),
% 0.20/0.50    inference(forward_demodulation,[],[f66,f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X0] : (k9_relat_1(sK0,X0) = k10_relat_1(k2_funct_1(sK0),X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f35,f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    v1_funct_1(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_funct_1(sK0) | k9_relat_1(sK0,X0) = k10_relat_1(k2_funct_1(sK0),X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f30,f20])).
% 0.20/0.50  % (20864)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    v1_relat_1(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_relat_1(sK0) | ~v1_funct_1(sK0) | k9_relat_1(sK0,X0) = k10_relat_1(k2_funct_1(sK0),X0)) )),
% 0.20/0.50    inference(resolution,[],[f17,f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    v2_funct_1(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK0)) | k9_relat_1(k2_funct_1(sK0),k10_relat_1(k2_funct_1(sK0),X1)) = X1) )),
% 0.20/0.50    inference(forward_demodulation,[],[f65,f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f33,f21])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ~v1_funct_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f29,f20])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.20/0.50    inference(resolution,[],[f17,f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ( ! [X1] : (~r1_tarski(X1,k2_relat_1(k2_funct_1(sK0))) | k9_relat_1(k2_funct_1(sK0),k10_relat_1(k2_funct_1(sK0),X1)) = X1) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f57,f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    v1_funct_1(k2_funct_1(sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f38,f21])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ~v1_funct_1(sK0) | v1_funct_1(k2_funct_1(sK0))),
% 0.20/0.50    inference(resolution,[],[f20,f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X1] : (~v1_funct_1(k2_funct_1(sK0)) | ~r1_tarski(X1,k2_relat_1(k2_funct_1(sK0))) | k9_relat_1(k2_funct_1(sK0),k10_relat_1(k2_funct_1(sK0),X1)) = X1) )),
% 0.20/0.50    inference(resolution,[],[f43,f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    v1_relat_1(k2_funct_1(sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f37,f21])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ~v1_funct_1(sK0) | v1_relat_1(k2_funct_1(sK0))),
% 0.20/0.50    inference(resolution,[],[f20,f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (20880)------------------------------
% 0.20/0.51  % (20880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (20880)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (20880)Memory used [KB]: 1663
% 0.20/0.51  % (20880)Time elapsed: 0.093 s
% 0.20/0.51  % (20880)------------------------------
% 0.20/0.51  % (20880)------------------------------
% 0.20/0.51  % (20882)Refutation not found, incomplete strategy% (20882)------------------------------
% 0.20/0.51  % (20882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (20882)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (20882)Memory used [KB]: 10618
% 0.20/0.51  % (20882)Time elapsed: 0.049 s
% 0.20/0.51  % (20882)------------------------------
% 0.20/0.51  % (20882)------------------------------
% 0.20/0.51  % (20857)Success in time 0.149 s
%------------------------------------------------------------------------------
