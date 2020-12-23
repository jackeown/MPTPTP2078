%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:48 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 201 expanded)
%              Number of leaves         :   11 (  72 expanded)
%              Depth                    :   16
%              Number of atoms          :  125 ( 767 expanded)
%              Number of equality atoms :   49 ( 211 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1360,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1358])).

fof(f1358,plain,(
    k7_relat_1(k5_relat_1(sK0,sK1),sK2) != k7_relat_1(k5_relat_1(sK0,sK1),sK2) ),
    inference(superposition,[],[f268,f1357])).

fof(f1357,plain,(
    ! [X0] : k7_relat_1(k5_relat_1(sK0,sK1),X0) = k7_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,k9_relat_1(sK0,X0))),X0) ),
    inference(forward_demodulation,[],[f1351,f62])).

fof(f62,plain,(
    ! [X6] : k7_relat_1(k5_relat_1(sK0,sK1),X6) = k5_relat_1(k7_relat_1(sK0,X6),sK1) ),
    inference(resolution,[],[f57,f24])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k5_relat_1(k7_relat_1(sK0,sK2),k7_relat_1(sK1,k9_relat_1(sK0,sK2))) != k7_relat_1(k5_relat_1(sK0,sK1),sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f20,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,X1),X2)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] : k5_relat_1(k7_relat_1(sK0,X2),k7_relat_1(X1,k9_relat_1(sK0,X2))) != k7_relat_1(k5_relat_1(sK0,X1),X2)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ? [X2] : k5_relat_1(k7_relat_1(sK0,X2),k7_relat_1(X1,k9_relat_1(sK0,X2))) != k7_relat_1(k5_relat_1(sK0,X1),X2)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] : k5_relat_1(k7_relat_1(sK0,X2),k7_relat_1(sK1,k9_relat_1(sK0,X2))) != k7_relat_1(k5_relat_1(sK0,sK1),X2)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] : k5_relat_1(k7_relat_1(sK0,X2),k7_relat_1(sK1,k9_relat_1(sK0,X2))) != k7_relat_1(k5_relat_1(sK0,sK1),X2)
   => k5_relat_1(k7_relat_1(sK0,sK2),k7_relat_1(sK1,k9_relat_1(sK0,sK2))) != k7_relat_1(k5_relat_1(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,X1),X2)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,X1),X2)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) = k7_relat_1(k5_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) = k7_relat_1(k5_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_funct_1)).

fof(f57,plain,(
    ! [X8,X7] :
      ( ~ v1_relat_1(X7)
      | k7_relat_1(k5_relat_1(sK0,X7),X8) = k5_relat_1(k7_relat_1(sK0,X8),X7) ) ),
    inference(resolution,[],[f34,f22])).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

fof(f1351,plain,(
    ! [X0] : k5_relat_1(k7_relat_1(sK0,X0),sK1) = k7_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,k9_relat_1(sK0,X0))),X0) ),
    inference(superposition,[],[f1305,f102])).

fof(f102,plain,(
    ! [X1] : k7_relat_1(sK0,X1) = k7_relat_1(k5_relat_1(sK0,k6_relat_1(k9_relat_1(sK0,X1))),X1) ),
    inference(superposition,[],[f100,f60])).

fof(f60,plain,(
    ! [X4,X3] : k7_relat_1(k5_relat_1(sK0,k6_relat_1(X3)),X4) = k5_relat_1(k7_relat_1(sK0,X4),k6_relat_1(X3)) ),
    inference(resolution,[],[f57,f27])).

fof(f27,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f100,plain,(
    ! [X5] : k7_relat_1(sK0,X5) = k5_relat_1(k7_relat_1(sK0,X5),k6_relat_1(k9_relat_1(sK0,X5))) ),
    inference(forward_demodulation,[],[f97,f45])).

fof(f45,plain,(
    ! [X5] : k2_relat_1(k7_relat_1(sK0,X5)) = k9_relat_1(sK0,X5) ),
    inference(resolution,[],[f33,f22])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f97,plain,(
    ! [X5] : k7_relat_1(sK0,X5) = k5_relat_1(k7_relat_1(sK0,X5),k6_relat_1(k2_relat_1(k7_relat_1(sK0,X5)))) ),
    inference(resolution,[],[f35,f22])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = k5_relat_1(k7_relat_1(X0,X1),k6_relat_1(k2_relat_1(k7_relat_1(X0,X1)))) ) ),
    inference(resolution,[],[f29,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f1305,plain,(
    ! [X17,X16] : k7_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,X17)),X16) = k5_relat_1(k7_relat_1(k5_relat_1(sK0,k6_relat_1(X17)),X16),sK1) ),
    inference(forward_demodulation,[],[f1304,f60])).

fof(f1304,plain,(
    ! [X17,X16] : k5_relat_1(k5_relat_1(k7_relat_1(sK0,X16),k6_relat_1(X17)),sK1) = k7_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,X17)),X16) ),
    inference(forward_demodulation,[],[f1303,f240])).

fof(f240,plain,(
    ! [X10,X9] : k7_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,X9)),X10) = k5_relat_1(k7_relat_1(sK0,X10),k7_relat_1(sK1,X9)) ),
    inference(resolution,[],[f59,f24])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(k5_relat_1(sK0,k7_relat_1(X0,X1)),X2) = k5_relat_1(k7_relat_1(sK0,X2),k7_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f57,f31])).

fof(f1303,plain,(
    ! [X17,X16] : k5_relat_1(k5_relat_1(k7_relat_1(sK0,X16),k6_relat_1(X17)),sK1) = k5_relat_1(k7_relat_1(sK0,X16),k7_relat_1(sK1,X17)) ),
    inference(forward_demodulation,[],[f1289,f42])).

fof(f42,plain,(
    ! [X6] : k7_relat_1(sK1,X6) = k5_relat_1(k6_relat_1(X6),sK1) ),
    inference(resolution,[],[f32,f24])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f1289,plain,(
    ! [X17,X16] : k5_relat_1(k5_relat_1(k7_relat_1(sK0,X16),k6_relat_1(X17)),sK1) = k5_relat_1(k7_relat_1(sK0,X16),k5_relat_1(k6_relat_1(X17),sK1)) ),
    inference(resolution,[],[f354,f27])).

fof(f354,plain,(
    ! [X8,X7] :
      ( ~ v1_relat_1(X8)
      | k5_relat_1(k5_relat_1(k7_relat_1(sK0,X7),X8),sK1) = k5_relat_1(k7_relat_1(sK0,X7),k5_relat_1(X8,sK1)) ) ),
    inference(resolution,[],[f80,f22])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(k7_relat_1(X1,X2),X0),sK1) = k5_relat_1(k7_relat_1(X1,X2),k5_relat_1(X0,sK1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f70,f31])).

fof(f70,plain,(
    ! [X10,X9] :
      ( ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | k5_relat_1(k5_relat_1(X9,X10),sK1) = k5_relat_1(X9,k5_relat_1(X10,sK1)) ) ),
    inference(resolution,[],[f30,f24])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f268,plain,(
    k7_relat_1(k5_relat_1(sK0,sK1),sK2) != k7_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,k9_relat_1(sK0,sK2))),sK2) ),
    inference(superposition,[],[f26,f240])).

fof(f26,plain,(
    k5_relat_1(k7_relat_1(sK0,sK2),k7_relat_1(sK1,k9_relat_1(sK0,sK2))) != k7_relat_1(k5_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:52:19 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.50  % (8461)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.50  % (8462)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.50  % (8468)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.51  % (8465)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (8479)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.51  % (8480)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.51  % (8474)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.51  % (8463)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % (8464)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (8463)Refutation not found, incomplete strategy% (8463)------------------------------
% 0.22/0.51  % (8463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (8463)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (8463)Memory used [KB]: 10490
% 0.22/0.51  % (8463)Time elapsed: 0.093 s
% 0.22/0.51  % (8463)------------------------------
% 0.22/0.51  % (8463)------------------------------
% 0.22/0.52  % (8482)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.52  % (8467)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (8481)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.52  % (8472)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.52  % (8470)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.52  % (8475)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.52  % (8469)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.26/0.53  % (8471)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.26/0.53  % (8473)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.26/0.53  % (8477)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.26/0.53  % (8478)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.26/0.53  % (8483)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.26/0.54  % (8466)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.26/0.54  % (8460)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.26/0.54  % (8483)Refutation not found, incomplete strategy% (8483)------------------------------
% 1.26/0.54  % (8483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.54  % (8483)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.54  
% 1.26/0.54  % (8483)Memory used [KB]: 10618
% 1.26/0.54  % (8483)Time elapsed: 0.103 s
% 1.26/0.54  % (8483)------------------------------
% 1.26/0.54  % (8483)------------------------------
% 1.26/0.54  % (8476)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.44/0.62  % (8469)Refutation found. Thanks to Tanya!
% 1.44/0.62  % SZS status Theorem for theBenchmark
% 1.44/0.62  % SZS output start Proof for theBenchmark
% 1.44/0.62  fof(f1360,plain,(
% 1.44/0.62    $false),
% 1.44/0.62    inference(trivial_inequality_removal,[],[f1358])).
% 1.44/0.62  fof(f1358,plain,(
% 1.44/0.62    k7_relat_1(k5_relat_1(sK0,sK1),sK2) != k7_relat_1(k5_relat_1(sK0,sK1),sK2)),
% 1.44/0.62    inference(superposition,[],[f268,f1357])).
% 1.44/0.62  fof(f1357,plain,(
% 1.44/0.62    ( ! [X0] : (k7_relat_1(k5_relat_1(sK0,sK1),X0) = k7_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,k9_relat_1(sK0,X0))),X0)) )),
% 1.44/0.62    inference(forward_demodulation,[],[f1351,f62])).
% 1.44/0.62  fof(f62,plain,(
% 1.44/0.62    ( ! [X6] : (k7_relat_1(k5_relat_1(sK0,sK1),X6) = k5_relat_1(k7_relat_1(sK0,X6),sK1)) )),
% 1.44/0.62    inference(resolution,[],[f57,f24])).
% 1.44/0.62  fof(f24,plain,(
% 1.44/0.62    v1_relat_1(sK1)),
% 1.44/0.62    inference(cnf_transformation,[],[f21])).
% 1.44/0.62  fof(f21,plain,(
% 1.44/0.62    (k5_relat_1(k7_relat_1(sK0,sK2),k7_relat_1(sK1,k9_relat_1(sK0,sK2))) != k7_relat_1(k5_relat_1(sK0,sK1),sK2) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.44/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f20,f19,f18])).
% 1.44/0.62  fof(f18,plain,(
% 1.44/0.62    ? [X0] : (? [X1] : (? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,X1),X2) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : k5_relat_1(k7_relat_1(sK0,X2),k7_relat_1(X1,k9_relat_1(sK0,X2))) != k7_relat_1(k5_relat_1(sK0,X1),X2) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.44/0.62    introduced(choice_axiom,[])).
% 1.44/0.62  fof(f19,plain,(
% 1.44/0.62    ? [X1] : (? [X2] : k5_relat_1(k7_relat_1(sK0,X2),k7_relat_1(X1,k9_relat_1(sK0,X2))) != k7_relat_1(k5_relat_1(sK0,X1),X2) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : k5_relat_1(k7_relat_1(sK0,X2),k7_relat_1(sK1,k9_relat_1(sK0,X2))) != k7_relat_1(k5_relat_1(sK0,sK1),X2) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.44/0.62    introduced(choice_axiom,[])).
% 1.44/0.62  fof(f20,plain,(
% 1.44/0.62    ? [X2] : k5_relat_1(k7_relat_1(sK0,X2),k7_relat_1(sK1,k9_relat_1(sK0,X2))) != k7_relat_1(k5_relat_1(sK0,sK1),X2) => k5_relat_1(k7_relat_1(sK0,sK2),k7_relat_1(sK1,k9_relat_1(sK0,sK2))) != k7_relat_1(k5_relat_1(sK0,sK1),sK2)),
% 1.44/0.62    introduced(choice_axiom,[])).
% 1.44/0.62  fof(f11,plain,(
% 1.44/0.62    ? [X0] : (? [X1] : (? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,X1),X2) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.44/0.62    inference(flattening,[],[f10])).
% 1.44/0.62  fof(f10,plain,(
% 1.44/0.62    ? [X0] : (? [X1] : (? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,X1),X2) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.44/0.62    inference(ennf_transformation,[],[f9])).
% 1.44/0.62  fof(f9,negated_conjecture,(
% 1.44/0.62    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) = k7_relat_1(k5_relat_1(X0,X1),X2)))),
% 1.44/0.62    inference(negated_conjecture,[],[f8])).
% 1.44/0.62  fof(f8,conjecture,(
% 1.44/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) = k7_relat_1(k5_relat_1(X0,X1),X2)))),
% 1.44/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_funct_1)).
% 1.44/0.62  fof(f57,plain,(
% 1.44/0.62    ( ! [X8,X7] : (~v1_relat_1(X7) | k7_relat_1(k5_relat_1(sK0,X7),X8) = k5_relat_1(k7_relat_1(sK0,X8),X7)) )),
% 1.44/0.62    inference(resolution,[],[f34,f22])).
% 1.44/0.62  fof(f22,plain,(
% 1.44/0.62    v1_relat_1(sK0)),
% 1.44/0.62    inference(cnf_transformation,[],[f21])).
% 1.44/0.62  fof(f34,plain,(
% 1.44/0.62    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)) )),
% 1.44/0.62    inference(cnf_transformation,[],[f17])).
% 1.44/0.62  fof(f17,plain,(
% 1.44/0.62    ! [X0,X1] : (! [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.44/0.62    inference(ennf_transformation,[],[f2])).
% 1.44/0.62  fof(f2,axiom,(
% 1.44/0.62    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 1.44/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).
% 1.44/0.62  fof(f1351,plain,(
% 1.44/0.62    ( ! [X0] : (k5_relat_1(k7_relat_1(sK0,X0),sK1) = k7_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,k9_relat_1(sK0,X0))),X0)) )),
% 1.44/0.62    inference(superposition,[],[f1305,f102])).
% 1.44/0.62  fof(f102,plain,(
% 1.44/0.62    ( ! [X1] : (k7_relat_1(sK0,X1) = k7_relat_1(k5_relat_1(sK0,k6_relat_1(k9_relat_1(sK0,X1))),X1)) )),
% 1.44/0.62    inference(superposition,[],[f100,f60])).
% 1.44/0.62  fof(f60,plain,(
% 1.44/0.62    ( ! [X4,X3] : (k7_relat_1(k5_relat_1(sK0,k6_relat_1(X3)),X4) = k5_relat_1(k7_relat_1(sK0,X4),k6_relat_1(X3))) )),
% 1.44/0.62    inference(resolution,[],[f57,f27])).
% 1.44/0.62  fof(f27,plain,(
% 1.44/0.62    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.44/0.62    inference(cnf_transformation,[],[f7])).
% 1.44/0.62  fof(f7,axiom,(
% 1.44/0.62    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.44/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.44/0.62  fof(f100,plain,(
% 1.44/0.62    ( ! [X5] : (k7_relat_1(sK0,X5) = k5_relat_1(k7_relat_1(sK0,X5),k6_relat_1(k9_relat_1(sK0,X5)))) )),
% 1.44/0.62    inference(forward_demodulation,[],[f97,f45])).
% 1.44/0.62  fof(f45,plain,(
% 1.44/0.62    ( ! [X5] : (k2_relat_1(k7_relat_1(sK0,X5)) = k9_relat_1(sK0,X5)) )),
% 1.44/0.62    inference(resolution,[],[f33,f22])).
% 1.44/0.62  fof(f33,plain,(
% 1.44/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.44/0.62    inference(cnf_transformation,[],[f16])).
% 1.44/0.62  fof(f16,plain,(
% 1.44/0.62    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.44/0.62    inference(ennf_transformation,[],[f3])).
% 1.44/0.62  fof(f3,axiom,(
% 1.44/0.62    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.44/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.44/0.62  fof(f97,plain,(
% 1.44/0.62    ( ! [X5] : (k7_relat_1(sK0,X5) = k5_relat_1(k7_relat_1(sK0,X5),k6_relat_1(k2_relat_1(k7_relat_1(sK0,X5))))) )),
% 1.44/0.62    inference(resolution,[],[f35,f22])).
% 1.44/0.62  fof(f35,plain,(
% 1.44/0.62    ( ! [X0,X1] : (~v1_relat_1(X0) | k7_relat_1(X0,X1) = k5_relat_1(k7_relat_1(X0,X1),k6_relat_1(k2_relat_1(k7_relat_1(X0,X1))))) )),
% 1.44/0.62    inference(resolution,[],[f29,f31])).
% 1.44/0.62  fof(f31,plain,(
% 1.44/0.62    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.44/0.62    inference(cnf_transformation,[],[f14])).
% 1.44/0.62  fof(f14,plain,(
% 1.44/0.62    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.44/0.62    inference(ennf_transformation,[],[f1])).
% 1.44/0.62  fof(f1,axiom,(
% 1.44/0.62    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.44/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.44/0.62  fof(f29,plain,(
% 1.44/0.62    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 1.44/0.62    inference(cnf_transformation,[],[f12])).
% 1.44/0.62  fof(f12,plain,(
% 1.44/0.62    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.44/0.62    inference(ennf_transformation,[],[f5])).
% 1.44/0.62  fof(f5,axiom,(
% 1.44/0.62    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.44/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 1.44/0.62  fof(f1305,plain,(
% 1.44/0.62    ( ! [X17,X16] : (k7_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,X17)),X16) = k5_relat_1(k7_relat_1(k5_relat_1(sK0,k6_relat_1(X17)),X16),sK1)) )),
% 1.44/0.62    inference(forward_demodulation,[],[f1304,f60])).
% 1.44/0.62  fof(f1304,plain,(
% 1.44/0.62    ( ! [X17,X16] : (k5_relat_1(k5_relat_1(k7_relat_1(sK0,X16),k6_relat_1(X17)),sK1) = k7_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,X17)),X16)) )),
% 1.44/0.62    inference(forward_demodulation,[],[f1303,f240])).
% 1.44/0.62  fof(f240,plain,(
% 1.44/0.62    ( ! [X10,X9] : (k7_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,X9)),X10) = k5_relat_1(k7_relat_1(sK0,X10),k7_relat_1(sK1,X9))) )),
% 1.44/0.62    inference(resolution,[],[f59,f24])).
% 1.44/0.62  fof(f59,plain,(
% 1.44/0.62    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k7_relat_1(k5_relat_1(sK0,k7_relat_1(X0,X1)),X2) = k5_relat_1(k7_relat_1(sK0,X2),k7_relat_1(X0,X1))) )),
% 1.44/0.62    inference(resolution,[],[f57,f31])).
% 1.44/0.62  fof(f1303,plain,(
% 1.44/0.62    ( ! [X17,X16] : (k5_relat_1(k5_relat_1(k7_relat_1(sK0,X16),k6_relat_1(X17)),sK1) = k5_relat_1(k7_relat_1(sK0,X16),k7_relat_1(sK1,X17))) )),
% 1.44/0.62    inference(forward_demodulation,[],[f1289,f42])).
% 1.44/0.62  fof(f42,plain,(
% 1.44/0.62    ( ! [X6] : (k7_relat_1(sK1,X6) = k5_relat_1(k6_relat_1(X6),sK1)) )),
% 1.44/0.62    inference(resolution,[],[f32,f24])).
% 1.44/0.62  fof(f32,plain,(
% 1.44/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 1.44/0.62    inference(cnf_transformation,[],[f15])).
% 1.44/0.62  fof(f15,plain,(
% 1.44/0.62    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.44/0.62    inference(ennf_transformation,[],[f6])).
% 1.44/0.62  fof(f6,axiom,(
% 1.44/0.62    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.44/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.44/0.62  fof(f1289,plain,(
% 1.44/0.62    ( ! [X17,X16] : (k5_relat_1(k5_relat_1(k7_relat_1(sK0,X16),k6_relat_1(X17)),sK1) = k5_relat_1(k7_relat_1(sK0,X16),k5_relat_1(k6_relat_1(X17),sK1))) )),
% 1.44/0.62    inference(resolution,[],[f354,f27])).
% 1.44/0.62  fof(f354,plain,(
% 1.44/0.62    ( ! [X8,X7] : (~v1_relat_1(X8) | k5_relat_1(k5_relat_1(k7_relat_1(sK0,X7),X8),sK1) = k5_relat_1(k7_relat_1(sK0,X7),k5_relat_1(X8,sK1))) )),
% 1.44/0.62    inference(resolution,[],[f80,f22])).
% 1.44/0.62  fof(f80,plain,(
% 1.44/0.62    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(k7_relat_1(X1,X2),X0),sK1) = k5_relat_1(k7_relat_1(X1,X2),k5_relat_1(X0,sK1)) | ~v1_relat_1(X0)) )),
% 1.44/0.62    inference(resolution,[],[f70,f31])).
% 1.44/0.62  fof(f70,plain,(
% 1.44/0.62    ( ! [X10,X9] : (~v1_relat_1(X9) | ~v1_relat_1(X10) | k5_relat_1(k5_relat_1(X9,X10),sK1) = k5_relat_1(X9,k5_relat_1(X10,sK1))) )),
% 1.44/0.62    inference(resolution,[],[f30,f24])).
% 1.44/0.62  fof(f30,plain,(
% 1.44/0.62    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.44/0.62    inference(cnf_transformation,[],[f13])).
% 1.44/0.62  fof(f13,plain,(
% 1.44/0.62    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.44/0.62    inference(ennf_transformation,[],[f4])).
% 1.44/0.62  fof(f4,axiom,(
% 1.44/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 1.44/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 1.44/0.62  fof(f268,plain,(
% 1.44/0.62    k7_relat_1(k5_relat_1(sK0,sK1),sK2) != k7_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,k9_relat_1(sK0,sK2))),sK2)),
% 1.44/0.62    inference(superposition,[],[f26,f240])).
% 1.44/0.62  fof(f26,plain,(
% 1.44/0.62    k5_relat_1(k7_relat_1(sK0,sK2),k7_relat_1(sK1,k9_relat_1(sK0,sK2))) != k7_relat_1(k5_relat_1(sK0,sK1),sK2)),
% 1.44/0.62    inference(cnf_transformation,[],[f21])).
% 1.44/0.62  % SZS output end Proof for theBenchmark
% 1.44/0.62  % (8469)------------------------------
% 1.44/0.62  % (8469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.62  % (8469)Termination reason: Refutation
% 1.44/0.62  
% 1.44/0.62  % (8469)Memory used [KB]: 3198
% 1.44/0.62  % (8469)Time elapsed: 0.203 s
% 1.44/0.62  % (8469)------------------------------
% 1.44/0.62  % (8469)------------------------------
% 1.44/0.62  % (8459)Success in time 0.249 s
%------------------------------------------------------------------------------
