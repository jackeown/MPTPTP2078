%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:01 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   38 (  63 expanded)
%              Number of leaves         :    7 (  16 expanded)
%              Depth                    :   15
%              Number of atoms          :  124 ( 191 expanded)
%              Number of equality atoms :    5 (  11 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(subsumption_resolution,[],[f67,f19])).

fof(f19,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => v5_funct_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v5_funct_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

fof(f67,plain,(
    ~ v1_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f66,f18])).

fof(f18,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f66,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(resolution,[],[f65,f20])).

fof(f20,plain,(
    ~ v5_funct_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X0] :
      ( v5_funct_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f64,f35])).

fof(f35,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f27,f22])).

fof(f22,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f27,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v5_funct_1(k1_xboole_0,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f63,f36])).

fof(f36,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f26,f22])).

fof(f26,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v5_funct_1(k1_xboole_0,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v5_funct_1(k1_xboole_0,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(X0)
      | v5_funct_1(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f59,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k1_relat_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | v5_funct_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(X0,k1_xboole_0),X1)
      | ~ v1_relat_1(X0)
      | v5_funct_1(k1_xboole_0,X0)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f58,f25])).

fof(f25,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v5_funct_1(k1_xboole_0,X0)
      | ~ r2_hidden(sK1(X0,k1_xboole_0),X1)
      | ~ r1_xboole_0(X1,k1_xboole_0) ) ),
    inference(resolution,[],[f57,f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
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

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v5_funct_1(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f56,f35])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(X0)
      | v5_funct_1(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f55,f36])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(X0)
      | v5_funct_1(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f30,f23])).

fof(f23,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n024.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 18:02:21 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.50  % (26035)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.23/0.50  % (26033)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.23/0.50  % (26046)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.23/0.50  % (26037)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.23/0.50  % (26038)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.23/0.50  % (26045)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.23/0.51  % (26038)Refutation not found, incomplete strategy% (26038)------------------------------
% 0.23/0.51  % (26038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (26038)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.51  
% 0.23/0.51  % (26038)Memory used [KB]: 10618
% 0.23/0.51  % (26038)Time elapsed: 0.088 s
% 0.23/0.51  % (26038)------------------------------
% 0.23/0.51  % (26038)------------------------------
% 0.23/0.51  % (26035)Refutation not found, incomplete strategy% (26035)------------------------------
% 0.23/0.51  % (26035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (26035)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.51  
% 0.23/0.51  % (26035)Memory used [KB]: 10490
% 0.23/0.51  % (26035)Time elapsed: 0.086 s
% 0.23/0.51  % (26035)------------------------------
% 0.23/0.51  % (26035)------------------------------
% 0.23/0.51  % (26052)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.23/0.51  % (26034)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.23/0.51  % (26043)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.23/0.51  % (26048)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.23/0.51  % (26048)Refutation not found, incomplete strategy% (26048)------------------------------
% 0.23/0.51  % (26048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (26048)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.51  
% 0.23/0.51  % (26048)Memory used [KB]: 1535
% 0.23/0.51  % (26048)Time elapsed: 0.001 s
% 0.23/0.51  % (26048)------------------------------
% 0.23/0.51  % (26048)------------------------------
% 0.23/0.51  % (26032)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.23/0.51  % (26053)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.23/0.51  % (26045)Refutation found. Thanks to Tanya!
% 0.23/0.51  % SZS status Theorem for theBenchmark
% 0.23/0.51  % SZS output start Proof for theBenchmark
% 0.23/0.51  fof(f68,plain,(
% 0.23/0.51    $false),
% 0.23/0.51    inference(subsumption_resolution,[],[f67,f19])).
% 0.23/0.51  fof(f19,plain,(
% 0.23/0.51    v1_funct_1(sK0)),
% 0.23/0.51    inference(cnf_transformation,[],[f13])).
% 0.23/0.51  fof(f13,plain,(
% 0.23/0.51    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.23/0.51    inference(flattening,[],[f12])).
% 0.23/0.51  fof(f12,plain,(
% 0.23/0.51    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f10])).
% 0.23/0.51  fof(f10,negated_conjecture,(
% 0.23/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.23/0.51    inference(negated_conjecture,[],[f9])).
% 0.23/0.51  fof(f9,conjecture,(
% 0.23/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).
% 0.23/0.51  fof(f67,plain,(
% 0.23/0.51    ~v1_funct_1(sK0)),
% 0.23/0.51    inference(subsumption_resolution,[],[f66,f18])).
% 0.23/0.51  fof(f18,plain,(
% 0.23/0.51    v1_relat_1(sK0)),
% 0.23/0.51    inference(cnf_transformation,[],[f13])).
% 0.23/0.51  fof(f66,plain,(
% 0.23/0.51    ~v1_relat_1(sK0) | ~v1_funct_1(sK0)),
% 0.23/0.51    inference(resolution,[],[f65,f20])).
% 0.23/0.51  fof(f20,plain,(
% 0.23/0.51    ~v5_funct_1(k1_xboole_0,sK0)),
% 0.23/0.51    inference(cnf_transformation,[],[f13])).
% 0.23/0.51  fof(f65,plain,(
% 0.23/0.51    ( ! [X0] : (v5_funct_1(k1_xboole_0,X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0)) )),
% 0.23/0.51    inference(subsumption_resolution,[],[f64,f35])).
% 0.23/0.51  fof(f35,plain,(
% 0.23/0.51    v1_funct_1(k1_xboole_0)),
% 0.23/0.51    inference(superposition,[],[f27,f22])).
% 0.23/0.51  fof(f22,plain,(
% 0.23/0.51    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.23/0.51    inference(cnf_transformation,[],[f5])).
% 0.23/0.51  fof(f5,axiom,(
% 0.23/0.51    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.23/0.51  fof(f27,plain,(
% 0.23/0.51    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f8])).
% 0.23/0.51  fof(f8,axiom,(
% 0.23/0.51    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.23/0.51  fof(f64,plain,(
% 0.23/0.51    ( ! [X0] : (~v1_relat_1(X0) | v5_funct_1(k1_xboole_0,X0) | ~v1_funct_1(X0) | ~v1_funct_1(k1_xboole_0)) )),
% 0.23/0.51    inference(subsumption_resolution,[],[f63,f36])).
% 0.23/0.51  fof(f36,plain,(
% 0.23/0.51    v1_relat_1(k1_xboole_0)),
% 0.23/0.51    inference(superposition,[],[f26,f22])).
% 0.23/0.51  fof(f26,plain,(
% 0.23/0.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f8])).
% 0.23/0.51  fof(f63,plain,(
% 0.23/0.51    ( ! [X0] : (~v1_relat_1(X0) | v5_funct_1(k1_xboole_0,X0) | ~v1_funct_1(X0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0)) )),
% 0.23/0.51    inference(duplicate_literal_removal,[],[f60])).
% 0.23/0.51  fof(f60,plain,(
% 0.23/0.51    ( ! [X0] : (~v1_relat_1(X0) | v5_funct_1(k1_xboole_0,X0) | ~v1_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X0) | v5_funct_1(k1_xboole_0,X0)) )),
% 0.23/0.51    inference(resolution,[],[f59,f30])).
% 0.23/0.51  fof(f30,plain,(
% 0.23/0.51    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | v5_funct_1(X1,X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f16])).
% 0.23/0.51  fof(f16,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.23/0.51    inference(flattening,[],[f15])).
% 0.23/0.51  fof(f15,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f7])).
% 0.23/0.51  fof(f7,axiom,(
% 0.23/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).
% 0.23/0.51  fof(f59,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~r2_hidden(sK1(X0,k1_xboole_0),X1) | ~v1_relat_1(X0) | v5_funct_1(k1_xboole_0,X0) | ~v1_funct_1(X0)) )),
% 0.23/0.51    inference(subsumption_resolution,[],[f58,f25])).
% 0.23/0.51  fof(f25,plain,(
% 0.23/0.51    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f3])).
% 0.23/0.51  fof(f3,axiom,(
% 0.23/0.51    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.23/0.51  fof(f58,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v5_funct_1(k1_xboole_0,X0) | ~r2_hidden(sK1(X0,k1_xboole_0),X1) | ~r1_xboole_0(X1,k1_xboole_0)) )),
% 0.23/0.51    inference(resolution,[],[f57,f32])).
% 0.23/0.51  fof(f32,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f17])).
% 0.23/0.51  fof(f17,plain,(
% 0.23/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.23/0.51    inference(ennf_transformation,[],[f11])).
% 0.23/0.51  fof(f11,plain,(
% 0.23/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.23/0.51    inference(rectify,[],[f2])).
% 0.23/0.51  fof(f2,axiom,(
% 0.23/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.23/0.51  fof(f57,plain,(
% 0.23/0.51    ( ! [X0] : (r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v5_funct_1(k1_xboole_0,X0)) )),
% 0.23/0.51    inference(subsumption_resolution,[],[f56,f35])).
% 0.23/0.51  fof(f56,plain,(
% 0.23/0.51    ( ! [X0] : (r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0) | ~v1_funct_1(X0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X0) | v5_funct_1(k1_xboole_0,X0)) )),
% 0.23/0.51    inference(subsumption_resolution,[],[f55,f36])).
% 0.23/0.51  fof(f55,plain,(
% 0.23/0.51    ( ! [X0] : (r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0) | ~v1_funct_1(X0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X0) | v5_funct_1(k1_xboole_0,X0)) )),
% 0.23/0.51    inference(superposition,[],[f30,f23])).
% 0.23/0.51  fof(f23,plain,(
% 0.23/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.23/0.51    inference(cnf_transformation,[],[f4])).
% 0.23/0.51  fof(f4,axiom,(
% 0.23/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.23/0.51  % SZS output end Proof for theBenchmark
% 0.23/0.51  % (26045)------------------------------
% 0.23/0.51  % (26045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (26045)Termination reason: Refutation
% 0.23/0.51  
% 0.23/0.51  % (26045)Memory used [KB]: 6140
% 0.23/0.51  % (26045)Time elapsed: 0.104 s
% 0.23/0.51  % (26045)------------------------------
% 0.23/0.51  % (26045)------------------------------
% 0.23/0.51  % (26054)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.23/0.52  % (26031)Success in time 0.144 s
%------------------------------------------------------------------------------
