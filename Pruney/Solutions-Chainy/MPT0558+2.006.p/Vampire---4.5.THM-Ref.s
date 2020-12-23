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
% DateTime   : Thu Dec  3 12:49:57 EST 2020

% Result     : Theorem 2.70s
% Output     : Refutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   61 (  97 expanded)
%              Number of leaves         :   11 (  21 expanded)
%              Depth                    :   16
%              Number of atoms          :  149 ( 242 expanded)
%              Number of equality atoms :   37 (  61 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1931,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1930,f24])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

% (6177)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f1930,plain,(
    ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f1910,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f1910,plain,(
    ~ v1_relat_1(k7_relat_1(sK1,k2_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f1909,f25])).

fof(f25,plain,(
    k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f1909,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,k2_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f1908,f64])).

fof(f64,plain,(
    ! [X6] : k2_relat_1(k7_relat_1(sK1,X6)) = k9_relat_1(sK1,X6) ),
    inference(resolution,[],[f39,f24])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f1908,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK1)) = k2_relat_1(k7_relat_1(sK1,k2_relat_1(sK0)))
    | ~ v1_relat_1(k7_relat_1(sK1,k2_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f1896,f188])).

fof(f188,plain,(
    k5_relat_1(sK0,sK1) = k5_relat_1(sK0,k7_relat_1(sK1,k2_relat_1(sK0))) ),
    inference(superposition,[],[f182,f55])).

fof(f55,plain,(
    sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) ),
    inference(resolution,[],[f28,f26])).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f182,plain,(
    ! [X2] : k5_relat_1(k5_relat_1(sK0,k6_relat_1(X2)),sK1) = k5_relat_1(sK0,k7_relat_1(sK1,X2)) ),
    inference(forward_demodulation,[],[f179,f60])).

fof(f60,plain,(
    ! [X6] : k7_relat_1(sK1,X6) = k5_relat_1(k6_relat_1(X6),sK1) ),
    inference(resolution,[],[f38,f24])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f179,plain,(
    ! [X2] : k5_relat_1(k5_relat_1(sK0,k6_relat_1(X2)),sK1) = k5_relat_1(sK0,k5_relat_1(k6_relat_1(X2),sK1)) ),
    inference(resolution,[],[f176,f27])).

fof(f27,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f176,plain,(
    ! [X5] :
      ( ~ v1_relat_1(X5)
      | k5_relat_1(k5_relat_1(sK0,X5),sK1) = k5_relat_1(sK0,k5_relat_1(X5,sK1)) ) ),
    inference(resolution,[],[f142,f26])).

fof(f142,plain,(
    ! [X10,X9] :
      ( ~ v1_relat_1(X10)
      | ~ v1_relat_1(X9)
      | k5_relat_1(k5_relat_1(X10,X9),sK1) = k5_relat_1(X10,k5_relat_1(X9,sK1)) ) ),
    inference(resolution,[],[f30,f24])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f1896,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,k2_relat_1(sK0)))
    | k2_relat_1(k7_relat_1(sK1,k2_relat_1(sK0))) = k2_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,k2_relat_1(sK0)))) ),
    inference(resolution,[],[f1894,f89])).

fof(f89,plain,(
    ! [X5] :
      ( ~ r1_tarski(k1_relat_1(X5),k2_relat_1(sK0))
      | ~ v1_relat_1(X5)
      | k2_relat_1(k5_relat_1(sK0,X5)) = k2_relat_1(X5) ) ),
    inference(resolution,[],[f29,f26])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f1894,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0) ),
    inference(duplicate_literal_removal,[],[f1885])).

fof(f1885,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)
      | r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0) ) ),
    inference(resolution,[],[f1836,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f1836,plain,(
    ! [X10,X9] :
      ( r2_hidden(sK4(k1_relat_1(k7_relat_1(sK1,X9)),X10),X9)
      | r1_tarski(k1_relat_1(k7_relat_1(sK1,X9)),X10) ) ),
    inference(resolution,[],[f105,f24])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK4(k1_relat_1(k7_relat_1(X0,X1)),X2),X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X2) ) ),
    inference(resolution,[],[f103,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f97,f49])).

fof(f49,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X3),k7_relat_1(X0,X2))
      | r2_hidden(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(X1,X2)
      | ~ r2_hidden(k4_tarski(X1,X3),k7_relat_1(X0,X2))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f48,f37])).

fof(f48,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k7_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:06:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (6154)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (6162)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (6171)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (6149)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (6163)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (6170)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (6145)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (6155)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (6162)Refutation not found, incomplete strategy% (6162)------------------------------
% 0.21/0.52  % (6162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (6167)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (6162)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (6162)Memory used [KB]: 10618
% 0.21/0.52  % (6162)Time elapsed: 0.114 s
% 0.21/0.52  % (6162)------------------------------
% 0.21/0.52  % (6162)------------------------------
% 0.21/0.53  % (6146)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (6173)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (6150)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (6151)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (6147)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (6160)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (6155)Refutation not found, incomplete strategy% (6155)------------------------------
% 0.21/0.54  % (6155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (6155)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (6155)Memory used [KB]: 10746
% 0.21/0.54  % (6155)Time elapsed: 0.124 s
% 0.21/0.54  % (6155)------------------------------
% 0.21/0.54  % (6155)------------------------------
% 0.21/0.54  % (6172)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (6159)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (6169)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (6168)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (6174)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (6164)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (6165)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (6148)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (6161)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (6167)Refutation not found, incomplete strategy% (6167)------------------------------
% 0.21/0.55  % (6167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (6167)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (6167)Memory used [KB]: 10746
% 0.21/0.55  % (6167)Time elapsed: 0.097 s
% 0.21/0.55  % (6167)------------------------------
% 0.21/0.55  % (6167)------------------------------
% 0.21/0.55  % (6166)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (6156)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (6157)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (6153)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (6158)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (6152)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.55/0.57  % (6156)Refutation not found, incomplete strategy% (6156)------------------------------
% 1.55/0.57  % (6156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (6156)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (6156)Memory used [KB]: 10746
% 1.55/0.57  % (6156)Time elapsed: 0.149 s
% 1.55/0.57  % (6156)------------------------------
% 1.55/0.57  % (6156)------------------------------
% 2.23/0.66  % (6176)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.23/0.67  % (6175)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.23/0.71  % (6178)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.70/0.73  % (6151)Refutation found. Thanks to Tanya!
% 2.70/0.73  % SZS status Theorem for theBenchmark
% 2.70/0.73  % SZS output start Proof for theBenchmark
% 2.70/0.73  fof(f1931,plain,(
% 2.70/0.73    $false),
% 2.70/0.73    inference(subsumption_resolution,[],[f1930,f24])).
% 2.70/0.73  fof(f24,plain,(
% 2.70/0.73    v1_relat_1(sK1)),
% 2.70/0.73    inference(cnf_transformation,[],[f14])).
% 2.70/0.73  % (6177)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.70/0.73  fof(f14,plain,(
% 2.70/0.73    ? [X0] : (? [X1] : (k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.70/0.73    inference(ennf_transformation,[],[f12])).
% 2.70/0.73  fof(f12,negated_conjecture,(
% 2.70/0.73    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 2.70/0.73    inference(negated_conjecture,[],[f11])).
% 2.70/0.73  fof(f11,conjecture,(
% 2.70/0.73    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 2.70/0.73  fof(f1930,plain,(
% 2.70/0.73    ~v1_relat_1(sK1)),
% 2.70/0.73    inference(resolution,[],[f1910,f37])).
% 2.70/0.73  fof(f37,plain,(
% 2.70/0.73    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f20])).
% 2.70/0.73  fof(f20,plain,(
% 2.70/0.73    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.70/0.73    inference(ennf_transformation,[],[f5])).
% 2.70/0.73  fof(f5,axiom,(
% 2.70/0.73    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 2.70/0.73  fof(f1910,plain,(
% 2.70/0.73    ~v1_relat_1(k7_relat_1(sK1,k2_relat_1(sK0)))),
% 2.70/0.73    inference(subsumption_resolution,[],[f1909,f25])).
% 2.70/0.73  fof(f25,plain,(
% 2.70/0.73    k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))),
% 2.70/0.73    inference(cnf_transformation,[],[f14])).
% 2.70/0.73  fof(f1909,plain,(
% 2.70/0.73    k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0)) | ~v1_relat_1(k7_relat_1(sK1,k2_relat_1(sK0)))),
% 2.70/0.73    inference(forward_demodulation,[],[f1908,f64])).
% 2.70/0.73  fof(f64,plain,(
% 2.70/0.73    ( ! [X6] : (k2_relat_1(k7_relat_1(sK1,X6)) = k9_relat_1(sK1,X6)) )),
% 2.70/0.73    inference(resolution,[],[f39,f24])).
% 2.70/0.73  fof(f39,plain,(
% 2.70/0.73    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f22])).
% 2.70/0.73  fof(f22,plain,(
% 2.70/0.73    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.70/0.73    inference(ennf_transformation,[],[f6])).
% 2.70/0.73  fof(f6,axiom,(
% 2.70/0.73    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 2.70/0.73  fof(f1908,plain,(
% 2.70/0.73    k2_relat_1(k5_relat_1(sK0,sK1)) = k2_relat_1(k7_relat_1(sK1,k2_relat_1(sK0))) | ~v1_relat_1(k7_relat_1(sK1,k2_relat_1(sK0)))),
% 2.70/0.73    inference(forward_demodulation,[],[f1896,f188])).
% 2.70/0.73  fof(f188,plain,(
% 2.70/0.73    k5_relat_1(sK0,sK1) = k5_relat_1(sK0,k7_relat_1(sK1,k2_relat_1(sK0)))),
% 2.70/0.73    inference(superposition,[],[f182,f55])).
% 2.70/0.73  fof(f55,plain,(
% 2.70/0.73    sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))),
% 2.70/0.73    inference(resolution,[],[f28,f26])).
% 2.70/0.73  fof(f26,plain,(
% 2.70/0.73    v1_relat_1(sK0)),
% 2.70/0.73    inference(cnf_transformation,[],[f14])).
% 2.70/0.73  fof(f28,plain,(
% 2.70/0.73    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 2.70/0.73    inference(cnf_transformation,[],[f15])).
% 2.70/0.73  fof(f15,plain,(
% 2.70/0.73    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 2.70/0.73    inference(ennf_transformation,[],[f9])).
% 2.70/0.73  fof(f9,axiom,(
% 2.70/0.73    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 2.70/0.73  fof(f182,plain,(
% 2.70/0.73    ( ! [X2] : (k5_relat_1(k5_relat_1(sK0,k6_relat_1(X2)),sK1) = k5_relat_1(sK0,k7_relat_1(sK1,X2))) )),
% 2.70/0.73    inference(forward_demodulation,[],[f179,f60])).
% 2.70/0.73  fof(f60,plain,(
% 2.70/0.73    ( ! [X6] : (k7_relat_1(sK1,X6) = k5_relat_1(k6_relat_1(X6),sK1)) )),
% 2.70/0.73    inference(resolution,[],[f38,f24])).
% 2.70/0.73  fof(f38,plain,(
% 2.70/0.73    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f21])).
% 2.70/0.73  fof(f21,plain,(
% 2.70/0.73    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.70/0.73    inference(ennf_transformation,[],[f10])).
% 2.70/0.73  fof(f10,axiom,(
% 2.70/0.73    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 2.70/0.73  fof(f179,plain,(
% 2.70/0.73    ( ! [X2] : (k5_relat_1(k5_relat_1(sK0,k6_relat_1(X2)),sK1) = k5_relat_1(sK0,k5_relat_1(k6_relat_1(X2),sK1))) )),
% 2.70/0.73    inference(resolution,[],[f176,f27])).
% 2.70/0.73  fof(f27,plain,(
% 2.70/0.73    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.70/0.73    inference(cnf_transformation,[],[f4])).
% 2.70/0.73  fof(f4,axiom,(
% 2.70/0.73    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 2.70/0.73  fof(f176,plain,(
% 2.70/0.73    ( ! [X5] : (~v1_relat_1(X5) | k5_relat_1(k5_relat_1(sK0,X5),sK1) = k5_relat_1(sK0,k5_relat_1(X5,sK1))) )),
% 2.70/0.73    inference(resolution,[],[f142,f26])).
% 2.70/0.73  fof(f142,plain,(
% 2.70/0.73    ( ! [X10,X9] : (~v1_relat_1(X10) | ~v1_relat_1(X9) | k5_relat_1(k5_relat_1(X10,X9),sK1) = k5_relat_1(X10,k5_relat_1(X9,sK1))) )),
% 2.70/0.73    inference(resolution,[],[f30,f24])).
% 2.70/0.73  fof(f30,plain,(
% 2.70/0.73    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 2.70/0.73    inference(cnf_transformation,[],[f18])).
% 2.70/0.73  fof(f18,plain,(
% 2.70/0.73    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.70/0.73    inference(ennf_transformation,[],[f8])).
% 2.70/0.73  fof(f8,axiom,(
% 2.70/0.73    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 2.70/0.73  fof(f1896,plain,(
% 2.70/0.73    ~v1_relat_1(k7_relat_1(sK1,k2_relat_1(sK0))) | k2_relat_1(k7_relat_1(sK1,k2_relat_1(sK0))) = k2_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,k2_relat_1(sK0))))),
% 2.70/0.73    inference(resolution,[],[f1894,f89])).
% 2.70/0.73  fof(f89,plain,(
% 2.70/0.73    ( ! [X5] : (~r1_tarski(k1_relat_1(X5),k2_relat_1(sK0)) | ~v1_relat_1(X5) | k2_relat_1(k5_relat_1(sK0,X5)) = k2_relat_1(X5)) )),
% 2.70/0.73    inference(resolution,[],[f29,f26])).
% 2.70/0.73  fof(f29,plain,(
% 2.70/0.73    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f17])).
% 2.70/0.73  fof(f17,plain,(
% 2.70/0.73    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.70/0.73    inference(flattening,[],[f16])).
% 2.70/0.73  fof(f16,plain,(
% 2.70/0.73    ! [X0] : (! [X1] : ((k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.70/0.73    inference(ennf_transformation,[],[f7])).
% 2.70/0.73  fof(f7,axiom,(
% 2.70/0.73    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0))))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 2.70/0.73  fof(f1894,plain,(
% 2.70/0.73    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)) )),
% 2.70/0.73    inference(duplicate_literal_removal,[],[f1885])).
% 2.70/0.73  fof(f1885,plain,(
% 2.70/0.73    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0) | r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)) )),
% 2.70/0.73    inference(resolution,[],[f1836,f41])).
% 2.70/0.73  fof(f41,plain,(
% 2.70/0.73    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f23])).
% 2.70/0.73  fof(f23,plain,(
% 2.70/0.73    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 2.70/0.73    inference(ennf_transformation,[],[f13])).
% 2.70/0.73  fof(f13,plain,(
% 2.70/0.73    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 2.70/0.73    inference(unused_predicate_definition_removal,[],[f1])).
% 2.70/0.73  fof(f1,axiom,(
% 2.70/0.73    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.70/0.73  fof(f1836,plain,(
% 2.70/0.73    ( ! [X10,X9] : (r2_hidden(sK4(k1_relat_1(k7_relat_1(sK1,X9)),X10),X9) | r1_tarski(k1_relat_1(k7_relat_1(sK1,X9)),X10)) )),
% 2.70/0.73    inference(resolution,[],[f105,f24])).
% 2.70/0.73  fof(f105,plain,(
% 2.70/0.73    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(sK4(k1_relat_1(k7_relat_1(X0,X1)),X2),X1) | r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X2)) )),
% 2.70/0.73    inference(resolution,[],[f103,f40])).
% 2.70/0.73  fof(f40,plain,(
% 2.70/0.73    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f23])).
% 2.70/0.73  fof(f103,plain,(
% 2.70/0.73    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2) | r2_hidden(X0,X1)) )),
% 2.70/0.73    inference(resolution,[],[f97,f49])).
% 2.70/0.73  fof(f49,plain,(
% 2.70/0.73    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) )),
% 2.70/0.73    inference(equality_resolution,[],[f43])).
% 2.70/0.73  fof(f43,plain,(
% 2.70/0.73    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 2.70/0.73    inference(cnf_transformation,[],[f3])).
% 2.70/0.73  fof(f3,axiom,(
% 2.70/0.73    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 2.70/0.73  fof(f97,plain,(
% 2.70/0.73    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X1,X3),k7_relat_1(X0,X2)) | r2_hidden(X1,X2) | ~v1_relat_1(X0)) )),
% 2.70/0.73    inference(duplicate_literal_removal,[],[f95])).
% 2.70/0.73  fof(f95,plain,(
% 2.70/0.73    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(X1,X2) | ~r2_hidden(k4_tarski(X1,X3),k7_relat_1(X0,X2)) | ~v1_relat_1(X0)) )),
% 2.70/0.73    inference(resolution,[],[f48,f37])).
% 2.70/0.73  fof(f48,plain,(
% 2.70/0.73    ( ! [X4,X0,X3,X1] : (~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0) | r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1))) )),
% 2.70/0.73    inference(equality_resolution,[],[f34])).
% 2.70/0.73  fof(f34,plain,(
% 2.70/0.73    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X2) | r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2) | k7_relat_1(X0,X1) != X2) )),
% 2.70/0.73    inference(cnf_transformation,[],[f19])).
% 2.70/0.73  fof(f19,plain,(
% 2.70/0.73    ! [X0] : (! [X1,X2] : ((k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 2.70/0.73    inference(ennf_transformation,[],[f2])).
% 2.70/0.73  fof(f2,axiom,(
% 2.70/0.73    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (v1_relat_1(X2) => (k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1))))))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).
% 2.70/0.73  % SZS output end Proof for theBenchmark
% 2.70/0.73  % (6151)------------------------------
% 2.70/0.73  % (6151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.70/0.73  % (6151)Termination reason: Refutation
% 2.70/0.73  
% 2.70/0.73  % (6151)Memory used [KB]: 8443
% 2.70/0.73  % (6151)Time elapsed: 0.295 s
% 2.70/0.73  % (6151)------------------------------
% 2.70/0.73  % (6151)------------------------------
% 2.70/0.73  % (6144)Success in time 0.375 s
%------------------------------------------------------------------------------
