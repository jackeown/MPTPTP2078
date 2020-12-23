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
% DateTime   : Thu Dec  3 12:54:17 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 101 expanded)
%              Number of leaves         :    7 (  23 expanded)
%              Depth                    :   16
%              Number of atoms          :  133 ( 321 expanded)
%              Number of equality atoms :   33 (  48 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f153,plain,(
    $false ),
    inference(subsumption_resolution,[],[f152,f21])).

% (474)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f21,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

% (475)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

fof(f152,plain,(
    r1_tarski(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f150])).

fof(f150,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f32,f141])).

fof(f141,plain,(
    k1_xboole_0 = k6_subset_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f140,f16])).

fof(f16,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f140,plain,
    ( k1_xboole_0 = k6_subset_1(sK0,sK1)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f138,f100])).

fof(f100,plain,(
    ! [X1] : r1_tarski(k6_subset_1(sK0,X1),k1_relat_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f98])).

fof(f98,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k6_subset_1(sK0,X1),k1_relat_1(sK2)) ) ),
    inference(superposition,[],[f32,f94])).

fof(f94,plain,(
    ! [X1] : k1_xboole_0 = k6_subset_1(k6_subset_1(sK0,X1),k1_relat_1(sK2)) ),
    inference(resolution,[],[f89,f31])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

% (490)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f89,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK0)
      | k1_xboole_0 = k6_subset_1(X3,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f87,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f23])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f87,plain,(
    ! [X0] :
      ( r1_tarski(X0,k1_relat_1(sK2))
      | ~ r1_tarski(X0,sK0) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( r1_tarski(X0,k1_relat_1(sK2))
      | ~ r1_tarski(X0,sK0)
      | r1_tarski(X0,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f75,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f75,plain,(
    ! [X14,X15] :
      ( r2_hidden(sK3(X14,X15),k1_relat_1(sK2))
      | r1_tarski(X14,X15)
      | ~ r1_tarski(X14,sK0) ) ),
    inference(resolution,[],[f68,f19])).

fof(f19,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_tarski(X3,X5)
      | r1_tarski(X2,X4)
      | r2_hidden(sK3(X2,X4),X5)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f54,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1),X2)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f25,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f138,plain,
    ( k1_xboole_0 = k6_subset_1(sK0,sK1)
    | ~ r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f137])).

fof(f137,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k6_subset_1(sK0,sK1)
    | ~ r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f24,f121])).

fof(f121,plain,(
    k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    inference(superposition,[],[f120,f38])).

fof(f38,plain,(
    k1_xboole_0 = k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f33,f18])).

fof(f18,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f120,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
    inference(subsumption_resolution,[],[f119,f16])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK2)
      | k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ) ),
    inference(subsumption_resolution,[],[f118,f17])).

fof(f17,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ) ),
    inference(resolution,[],[f30,f20])).

fof(f20,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f23])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:44:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.54  % (480)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.38/0.57  % (508)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.38/0.57  % (509)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.38/0.58  % (501)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.38/0.58  % (500)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.38/0.58  % (508)Refutation not found, incomplete strategy% (508)------------------------------
% 1.38/0.58  % (508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.58  % (488)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.38/0.58  % (472)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.66/0.59  % (508)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.59  
% 1.66/0.59  % (508)Memory used [KB]: 10618
% 1.66/0.59  % (508)Time elapsed: 0.148 s
% 1.66/0.59  % (508)------------------------------
% 1.66/0.59  % (508)------------------------------
% 1.66/0.60  % (488)Refutation found. Thanks to Tanya!
% 1.66/0.60  % SZS status Theorem for theBenchmark
% 1.66/0.60  % (470)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.66/0.60  % SZS output start Proof for theBenchmark
% 1.66/0.60  fof(f153,plain,(
% 1.66/0.60    $false),
% 1.66/0.60    inference(subsumption_resolution,[],[f152,f21])).
% 1.66/0.60  % (474)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.66/0.60  fof(f21,plain,(
% 1.66/0.60    ~r1_tarski(sK0,sK1)),
% 1.66/0.60    inference(cnf_transformation,[],[f10])).
% 1.66/0.60  fof(f10,plain,(
% 1.66/0.60    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.66/0.60    inference(flattening,[],[f9])).
% 1.66/0.60  % (475)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.66/0.60  fof(f9,plain,(
% 1.66/0.60    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.66/0.60    inference(ennf_transformation,[],[f8])).
% 1.66/0.60  fof(f8,negated_conjecture,(
% 1.66/0.60    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.66/0.60    inference(negated_conjecture,[],[f7])).
% 1.66/0.60  fof(f7,conjecture,(
% 1.66/0.60    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).
% 1.66/0.60  fof(f152,plain,(
% 1.66/0.60    r1_tarski(sK0,sK1)),
% 1.66/0.60    inference(trivial_inequality_removal,[],[f150])).
% 1.66/0.60  fof(f150,plain,(
% 1.66/0.60    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK1)),
% 1.66/0.60    inference(superposition,[],[f32,f141])).
% 1.66/0.60  fof(f141,plain,(
% 1.66/0.60    k1_xboole_0 = k6_subset_1(sK0,sK1)),
% 1.66/0.60    inference(subsumption_resolution,[],[f140,f16])).
% 1.66/0.60  fof(f16,plain,(
% 1.66/0.60    v1_relat_1(sK2)),
% 1.66/0.60    inference(cnf_transformation,[],[f10])).
% 1.66/0.60  fof(f140,plain,(
% 1.66/0.60    k1_xboole_0 = k6_subset_1(sK0,sK1) | ~v1_relat_1(sK2)),
% 1.66/0.60    inference(subsumption_resolution,[],[f138,f100])).
% 1.66/0.60  fof(f100,plain,(
% 1.66/0.60    ( ! [X1] : (r1_tarski(k6_subset_1(sK0,X1),k1_relat_1(sK2))) )),
% 1.66/0.60    inference(trivial_inequality_removal,[],[f98])).
% 1.66/0.60  fof(f98,plain,(
% 1.66/0.60    ( ! [X1] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k6_subset_1(sK0,X1),k1_relat_1(sK2))) )),
% 1.66/0.60    inference(superposition,[],[f32,f94])).
% 1.66/0.60  fof(f94,plain,(
% 1.66/0.60    ( ! [X1] : (k1_xboole_0 = k6_subset_1(k6_subset_1(sK0,X1),k1_relat_1(sK2))) )),
% 1.66/0.60    inference(resolution,[],[f89,f31])).
% 1.66/0.60  fof(f31,plain,(
% 1.66/0.60    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 1.66/0.60    inference(definition_unfolding,[],[f22,f23])).
% 1.66/0.60  fof(f23,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f4])).
% 1.66/0.60  fof(f4,axiom,(
% 1.66/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.66/0.60  fof(f22,plain,(
% 1.66/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f3])).
% 1.66/0.60  fof(f3,axiom,(
% 1.66/0.60    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.66/0.60  % (490)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.66/0.60  fof(f89,plain,(
% 1.66/0.60    ( ! [X3] : (~r1_tarski(X3,sK0) | k1_xboole_0 = k6_subset_1(X3,k1_relat_1(sK2))) )),
% 1.66/0.60    inference(resolution,[],[f87,f33])).
% 1.66/0.60  fof(f33,plain,(
% 1.66/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 1.66/0.60    inference(definition_unfolding,[],[f28,f23])).
% 1.66/0.60  fof(f28,plain,(
% 1.66/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.66/0.60    inference(cnf_transformation,[],[f2])).
% 1.66/0.60  fof(f2,axiom,(
% 1.66/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.66/0.60  fof(f87,plain,(
% 1.66/0.60    ( ! [X0] : (r1_tarski(X0,k1_relat_1(sK2)) | ~r1_tarski(X0,sK0)) )),
% 1.66/0.60    inference(duplicate_literal_removal,[],[f85])).
% 1.66/0.60  fof(f85,plain,(
% 1.66/0.60    ( ! [X0] : (r1_tarski(X0,k1_relat_1(sK2)) | ~r1_tarski(X0,sK0) | r1_tarski(X0,k1_relat_1(sK2))) )),
% 1.66/0.60    inference(resolution,[],[f75,f27])).
% 1.66/0.60  fof(f27,plain,(
% 1.66/0.60    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f13])).
% 1.66/0.60  fof(f13,plain,(
% 1.66/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.66/0.60    inference(ennf_transformation,[],[f1])).
% 1.66/0.60  fof(f1,axiom,(
% 1.66/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.66/0.60  fof(f75,plain,(
% 1.66/0.60    ( ! [X14,X15] : (r2_hidden(sK3(X14,X15),k1_relat_1(sK2)) | r1_tarski(X14,X15) | ~r1_tarski(X14,sK0)) )),
% 1.66/0.60    inference(resolution,[],[f68,f19])).
% 1.66/0.60  fof(f19,plain,(
% 1.66/0.60    r1_tarski(sK0,k1_relat_1(sK2))),
% 1.66/0.60    inference(cnf_transformation,[],[f10])).
% 1.66/0.60  fof(f68,plain,(
% 1.66/0.60    ( ! [X4,X2,X5,X3] : (~r1_tarski(X3,X5) | r1_tarski(X2,X4) | r2_hidden(sK3(X2,X4),X5) | ~r1_tarski(X2,X3)) )),
% 1.66/0.60    inference(resolution,[],[f54,f25])).
% 1.66/0.60  fof(f25,plain,(
% 1.66/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f13])).
% 1.66/0.60  fof(f54,plain,(
% 1.66/0.60    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1),X2) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1)) )),
% 1.66/0.60    inference(resolution,[],[f25,f26])).
% 1.66/0.60  fof(f26,plain,(
% 1.66/0.60    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f13])).
% 1.66/0.60  fof(f138,plain,(
% 1.66/0.60    k1_xboole_0 = k6_subset_1(sK0,sK1) | ~r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.66/0.60    inference(trivial_inequality_removal,[],[f137])).
% 1.66/0.60  fof(f137,plain,(
% 1.66/0.60    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k6_subset_1(sK0,sK1) | ~r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.66/0.60    inference(superposition,[],[f24,f121])).
% 1.66/0.60  fof(f121,plain,(
% 1.66/0.60    k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1))),
% 1.66/0.60    inference(superposition,[],[f120,f38])).
% 1.66/0.60  fof(f38,plain,(
% 1.66/0.60    k1_xboole_0 = k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 1.66/0.60    inference(resolution,[],[f33,f18])).
% 1.66/0.60  fof(f18,plain,(
% 1.66/0.60    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 1.66/0.60    inference(cnf_transformation,[],[f10])).
% 1.66/0.60  fof(f120,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f119,f16])).
% 1.66/0.60  fof(f119,plain,(
% 1.66/0.60    ( ! [X0,X1] : (~v1_relat_1(sK2) | k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f118,f17])).
% 1.66/0.60  fof(f17,plain,(
% 1.66/0.60    v1_funct_1(sK2)),
% 1.66/0.60    inference(cnf_transformation,[],[f10])).
% 1.66/0.60  fof(f118,plain,(
% 1.66/0.60    ( ! [X0,X1] : (~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) )),
% 1.66/0.60    inference(resolution,[],[f30,f20])).
% 1.66/0.60  fof(f20,plain,(
% 1.66/0.60    v2_funct_1(sK2)),
% 1.66/0.60    inference(cnf_transformation,[],[f10])).
% 1.66/0.60  fof(f30,plain,(
% 1.66/0.60    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) )),
% 1.66/0.60    inference(cnf_transformation,[],[f15])).
% 1.66/0.60  fof(f15,plain,(
% 1.66/0.60    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.66/0.60    inference(flattening,[],[f14])).
% 1.66/0.60  fof(f14,plain,(
% 1.66/0.60    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.66/0.60    inference(ennf_transformation,[],[f6])).
% 1.66/0.60  fof(f6,axiom,(
% 1.66/0.60    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).
% 1.66/0.60  fof(f24,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f12])).
% 1.66/0.60  fof(f12,plain,(
% 1.66/0.60    ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 1.66/0.60    inference(flattening,[],[f11])).
% 1.66/0.60  fof(f11,plain,(
% 1.66/0.60    ! [X0,X1] : ((k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 1.66/0.60    inference(ennf_transformation,[],[f5])).
% 1.66/0.60  fof(f5,axiom,(
% 1.66/0.60    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).
% 1.66/0.60  fof(f32,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 1.66/0.60    inference(definition_unfolding,[],[f29,f23])).
% 1.66/0.60  fof(f29,plain,(
% 1.66/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.66/0.60    inference(cnf_transformation,[],[f2])).
% 1.66/0.60  % SZS output end Proof for theBenchmark
% 1.66/0.60  % (488)------------------------------
% 1.66/0.60  % (488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.60  % (488)Termination reason: Refutation
% 1.66/0.60  
% 1.66/0.60  % (488)Memory used [KB]: 6268
% 1.66/0.60  % (488)Time elapsed: 0.103 s
% 1.66/0.61  % (488)------------------------------
% 1.66/0.61  % (488)------------------------------
% 1.66/0.61  % (473)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.66/0.61  % (464)Success in time 0.237 s
%------------------------------------------------------------------------------
