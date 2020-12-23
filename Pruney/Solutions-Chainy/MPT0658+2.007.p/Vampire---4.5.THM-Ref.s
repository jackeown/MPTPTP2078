%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 156 expanded)
%              Number of leaves         :    7 (  37 expanded)
%              Depth                    :   26
%              Number of atoms          :  240 ( 670 expanded)
%              Number of equality atoms :   75 ( 179 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f69,plain,(
    $false ),
    inference(subsumption_resolution,[],[f68,f22])).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( sK0 != k2_funct_1(k2_funct_1(sK0))
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( k2_funct_1(k2_funct_1(X0)) != X0
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( sK0 != k2_funct_1(k2_funct_1(sK0))
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( k2_funct_1(k2_funct_1(X0)) != X0
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( k2_funct_1(k2_funct_1(X0)) != X0
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

% (3479)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% (3480)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% (3470)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% (3470)Refutation not found, incomplete strategy% (3470)------------------------------
% (3470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3470)Termination reason: Refutation not found, incomplete strategy

% (3470)Memory used [KB]: 10490
% (3470)Time elapsed: 0.096 s
% (3470)------------------------------
% (3470)------------------------------
% (3478)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% (3476)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f68,plain,(
    ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f67,f23])).

fof(f23,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f66,f24])).

fof(f24,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f66,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(trivial_inequality_removal,[],[f65])).

fof(f65,plain,
    ( k2_relat_1(sK0) != k2_relat_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f64,f31])).

fof(f31,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f64,plain,(
    k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f63,f22])).

fof(f63,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f62,f23])).

fof(f62,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f61,f24])).

fof(f61,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(trivial_inequality_removal,[],[f60])).

fof(f60,plain,
    ( k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK0))
    | k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f59,f33])).

fof(f33,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f59,plain,
    ( k5_relat_1(sK0,k2_funct_1(sK0)) != k6_relat_1(k1_relat_1(sK0))
    | k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f58,f22])).

fof(f58,plain,
    ( k5_relat_1(sK0,k2_funct_1(sK0)) != k6_relat_1(k1_relat_1(sK0))
    | k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f57,f23])).

fof(f57,plain,
    ( k5_relat_1(sK0,k2_funct_1(sK0)) != k6_relat_1(k1_relat_1(sK0))
    | k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f56,f24])).

fof(f56,plain,
    ( k5_relat_1(sK0,k2_funct_1(sK0)) != k6_relat_1(k1_relat_1(sK0))
    | k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f53,f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,
    ( k6_relat_1(k2_relat_1(k2_funct_1(sK0))) != k5_relat_1(sK0,k2_funct_1(sK0))
    | k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f52,f22])).

fof(f52,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | k6_relat_1(k2_relat_1(k2_funct_1(sK0))) != k5_relat_1(sK0,k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f49,f25])).

fof(f25,plain,(
    sK0 != k2_funct_1(k2_funct_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,
    ( sK0 = k2_funct_1(k2_funct_1(sK0))
    | k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | k6_relat_1(k2_relat_1(k2_funct_1(sK0))) != k5_relat_1(sK0,k2_funct_1(sK0)) ),
    inference(resolution,[],[f46,f23])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k2_funct_1(k2_funct_1(sK0)) = X0
      | k2_relat_1(X0) != k1_relat_1(k2_funct_1(sK0))
      | ~ v1_relat_1(X0)
      | k6_relat_1(k2_relat_1(k2_funct_1(sK0))) != k5_relat_1(X0,k2_funct_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f45,f22])).

fof(f45,plain,(
    ! [X0] :
      ( k2_relat_1(X0) != k1_relat_1(k2_funct_1(sK0))
      | k2_funct_1(k2_funct_1(sK0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k6_relat_1(k2_relat_1(k2_funct_1(sK0))) != k5_relat_1(X0,k2_funct_1(sK0))
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f43,f23])).

fof(f43,plain,(
    ! [X0] :
      ( k2_relat_1(X0) != k1_relat_1(k2_funct_1(sK0))
      | k2_funct_1(k2_funct_1(sK0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k6_relat_1(k2_relat_1(k2_funct_1(sK0))) != k5_relat_1(X0,k2_funct_1(sK0))
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f41,f24])).

fof(f41,plain,(
    ! [X2,X1] :
      ( ~ v2_funct_1(X1)
      | k1_relat_1(k2_funct_1(X1)) != k2_relat_1(X2)
      | k2_funct_1(k2_funct_1(X1)) = X2
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k6_relat_1(k2_relat_1(k2_funct_1(X1))) != k5_relat_1(X2,k2_funct_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f40,f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
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

fof(f40,plain,(
    ! [X2,X1] :
      ( k6_relat_1(k2_relat_1(k2_funct_1(X1))) != k5_relat_1(X2,k2_funct_1(X1))
      | k1_relat_1(k2_funct_1(X1)) != k2_relat_1(X2)
      | k2_funct_1(k2_funct_1(X1)) = X2
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f37,f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X2,X1] :
      ( k6_relat_1(k2_relat_1(k2_funct_1(X1))) != k5_relat_1(X2,k2_funct_1(X1))
      | k1_relat_1(k2_funct_1(X1)) != k2_relat_1(X2)
      | k2_funct_1(k2_funct_1(X1)) = X2
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(k2_funct_1(X1))
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f35,f28])).

fof(f28,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | k2_funct_1(X0) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:34:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (3474)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (3474)Refutation not found, incomplete strategy% (3474)------------------------------
% 0.20/0.47  % (3474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (3474)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (3482)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.47  % (3474)Memory used [KB]: 6140
% 0.20/0.47  % (3474)Time elapsed: 0.061 s
% 0.20/0.47  % (3474)------------------------------
% 0.20/0.47  % (3474)------------------------------
% 0.20/0.48  % (3475)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.49  % (3477)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.49  % (3469)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.49  % (3485)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.50  % (3471)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.50  % (3477)Refutation not found, incomplete strategy% (3477)------------------------------
% 0.20/0.50  % (3477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (3477)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (3477)Memory used [KB]: 10490
% 0.20/0.50  % (3477)Time elapsed: 0.081 s
% 0.20/0.50  % (3477)------------------------------
% 0.20/0.50  % (3477)------------------------------
% 0.20/0.50  % (3486)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.50  % (3487)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.51  % (3486)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(subsumption_resolution,[],[f68,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    v1_relat_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    sK0 != k2_funct_1(k2_funct_1(sK0)) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ? [X0] : (k2_funct_1(k2_funct_1(X0)) != X0 & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (sK0 != k2_funct_1(k2_funct_1(sK0)) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ? [X0] : (k2_funct_1(k2_funct_1(X0)) != X0 & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f8])).
% 0.20/0.51  fof(f8,plain,(
% 0.20/0.51    ? [X0] : ((k2_funct_1(k2_funct_1(X0)) != X0 & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.20/0.51    inference(negated_conjecture,[],[f6])).
% 0.20/0.51  % (3479)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.51  % (3480)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.51  % (3470)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.51  % (3470)Refutation not found, incomplete strategy% (3470)------------------------------
% 0.20/0.51  % (3470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (3470)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (3470)Memory used [KB]: 10490
% 0.20/0.51  % (3470)Time elapsed: 0.096 s
% 0.20/0.51  % (3470)------------------------------
% 0.20/0.51  % (3470)------------------------------
% 1.28/0.52  % (3478)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.28/0.52  % (3476)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.28/0.52  fof(f6,conjecture,(
% 1.28/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 1.28/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 1.28/0.52  fof(f68,plain,(
% 1.28/0.52    ~v1_relat_1(sK0)),
% 1.28/0.52    inference(subsumption_resolution,[],[f67,f23])).
% 1.28/0.52  fof(f23,plain,(
% 1.28/0.52    v1_funct_1(sK0)),
% 1.28/0.52    inference(cnf_transformation,[],[f21])).
% 1.28/0.52  fof(f67,plain,(
% 1.28/0.52    ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.28/0.52    inference(subsumption_resolution,[],[f66,f24])).
% 1.28/0.52  fof(f24,plain,(
% 1.28/0.52    v2_funct_1(sK0)),
% 1.28/0.52    inference(cnf_transformation,[],[f21])).
% 1.28/0.52  fof(f66,plain,(
% 1.28/0.52    ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.28/0.52    inference(trivial_inequality_removal,[],[f65])).
% 1.28/0.52  fof(f65,plain,(
% 1.28/0.52    k2_relat_1(sK0) != k2_relat_1(sK0) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.28/0.52    inference(superposition,[],[f64,f31])).
% 1.28/0.52  fof(f31,plain,(
% 1.28/0.52    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.28/0.52    inference(cnf_transformation,[],[f15])).
% 1.28/0.52  fof(f15,plain,(
% 1.28/0.52    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.28/0.52    inference(flattening,[],[f14])).
% 1.28/0.52  fof(f14,plain,(
% 1.28/0.52    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.28/0.52    inference(ennf_transformation,[],[f3])).
% 1.28/0.52  fof(f3,axiom,(
% 1.28/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.28/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.28/0.52  fof(f64,plain,(
% 1.28/0.52    k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))),
% 1.28/0.52    inference(subsumption_resolution,[],[f63,f22])).
% 1.28/0.52  fof(f63,plain,(
% 1.28/0.52    k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0)),
% 1.28/0.52    inference(subsumption_resolution,[],[f62,f23])).
% 1.28/0.52  fof(f62,plain,(
% 1.28/0.52    k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.28/0.52    inference(subsumption_resolution,[],[f61,f24])).
% 1.28/0.52  fof(f61,plain,(
% 1.28/0.52    k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.28/0.52    inference(trivial_inequality_removal,[],[f60])).
% 1.28/0.52  fof(f60,plain,(
% 1.28/0.52    k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK0)) | k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.28/0.52    inference(superposition,[],[f59,f33])).
% 1.28/0.52  fof(f33,plain,(
% 1.28/0.52    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.28/0.52    inference(cnf_transformation,[],[f17])).
% 1.28/0.52  fof(f17,plain,(
% 1.28/0.52    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.28/0.52    inference(flattening,[],[f16])).
% 1.28/0.52  fof(f16,plain,(
% 1.28/0.52    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.28/0.52    inference(ennf_transformation,[],[f4])).
% 1.28/0.52  fof(f4,axiom,(
% 1.28/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.28/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 1.28/0.52  fof(f59,plain,(
% 1.28/0.52    k5_relat_1(sK0,k2_funct_1(sK0)) != k6_relat_1(k1_relat_1(sK0)) | k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))),
% 1.28/0.52    inference(subsumption_resolution,[],[f58,f22])).
% 1.28/0.52  fof(f58,plain,(
% 1.28/0.52    k5_relat_1(sK0,k2_funct_1(sK0)) != k6_relat_1(k1_relat_1(sK0)) | k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0)),
% 1.28/0.52    inference(subsumption_resolution,[],[f57,f23])).
% 1.28/0.52  fof(f57,plain,(
% 1.28/0.52    k5_relat_1(sK0,k2_funct_1(sK0)) != k6_relat_1(k1_relat_1(sK0)) | k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.28/0.52    inference(subsumption_resolution,[],[f56,f24])).
% 1.28/0.52  fof(f56,plain,(
% 1.28/0.52    k5_relat_1(sK0,k2_funct_1(sK0)) != k6_relat_1(k1_relat_1(sK0)) | k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.28/0.52    inference(superposition,[],[f53,f32])).
% 1.28/0.52  fof(f32,plain,(
% 1.28/0.52    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.28/0.52    inference(cnf_transformation,[],[f15])).
% 1.28/0.52  fof(f53,plain,(
% 1.28/0.52    k6_relat_1(k2_relat_1(k2_funct_1(sK0))) != k5_relat_1(sK0,k2_funct_1(sK0)) | k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))),
% 1.28/0.52    inference(subsumption_resolution,[],[f52,f22])).
% 1.28/0.52  fof(f52,plain,(
% 1.28/0.52    k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | k6_relat_1(k2_relat_1(k2_funct_1(sK0))) != k5_relat_1(sK0,k2_funct_1(sK0))),
% 1.28/0.52    inference(subsumption_resolution,[],[f49,f25])).
% 1.28/0.52  fof(f25,plain,(
% 1.28/0.52    sK0 != k2_funct_1(k2_funct_1(sK0))),
% 1.28/0.52    inference(cnf_transformation,[],[f21])).
% 1.28/0.52  fof(f49,plain,(
% 1.28/0.52    sK0 = k2_funct_1(k2_funct_1(sK0)) | k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | k6_relat_1(k2_relat_1(k2_funct_1(sK0))) != k5_relat_1(sK0,k2_funct_1(sK0))),
% 1.28/0.52    inference(resolution,[],[f46,f23])).
% 1.28/0.52  fof(f46,plain,(
% 1.28/0.52    ( ! [X0] : (~v1_funct_1(X0) | k2_funct_1(k2_funct_1(sK0)) = X0 | k2_relat_1(X0) != k1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(X0) | k6_relat_1(k2_relat_1(k2_funct_1(sK0))) != k5_relat_1(X0,k2_funct_1(sK0))) )),
% 1.28/0.52    inference(subsumption_resolution,[],[f45,f22])).
% 1.28/0.52  fof(f45,plain,(
% 1.28/0.52    ( ! [X0] : (k2_relat_1(X0) != k1_relat_1(k2_funct_1(sK0)) | k2_funct_1(k2_funct_1(sK0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k6_relat_1(k2_relat_1(k2_funct_1(sK0))) != k5_relat_1(X0,k2_funct_1(sK0)) | ~v1_relat_1(sK0)) )),
% 1.28/0.52    inference(subsumption_resolution,[],[f43,f23])).
% 1.28/0.52  fof(f43,plain,(
% 1.28/0.52    ( ! [X0] : (k2_relat_1(X0) != k1_relat_1(k2_funct_1(sK0)) | k2_funct_1(k2_funct_1(sK0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k6_relat_1(k2_relat_1(k2_funct_1(sK0))) != k5_relat_1(X0,k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) )),
% 1.28/0.52    inference(resolution,[],[f41,f24])).
% 1.28/0.52  fof(f41,plain,(
% 1.28/0.52    ( ! [X2,X1] : (~v2_funct_1(X1) | k1_relat_1(k2_funct_1(X1)) != k2_relat_1(X2) | k2_funct_1(k2_funct_1(X1)) = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | k6_relat_1(k2_relat_1(k2_funct_1(X1))) != k5_relat_1(X2,k2_funct_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.28/0.52    inference(subsumption_resolution,[],[f40,f29])).
% 1.28/0.52  fof(f29,plain,(
% 1.28/0.52    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.28/0.52    inference(cnf_transformation,[],[f13])).
% 1.28/0.52  fof(f13,plain,(
% 1.28/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.28/0.52    inference(flattening,[],[f12])).
% 1.28/0.52  fof(f12,plain,(
% 1.28/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.28/0.52    inference(ennf_transformation,[],[f1])).
% 1.28/0.52  fof(f1,axiom,(
% 1.28/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.28/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.28/0.52  fof(f40,plain,(
% 1.28/0.52    ( ! [X2,X1] : (k6_relat_1(k2_relat_1(k2_funct_1(X1))) != k5_relat_1(X2,k2_funct_1(X1)) | k1_relat_1(k2_funct_1(X1)) != k2_relat_1(X2) | k2_funct_1(k2_funct_1(X1)) = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(k2_funct_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.28/0.52    inference(subsumption_resolution,[],[f37,f30])).
% 1.28/0.52  fof(f30,plain,(
% 1.28/0.52    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.28/0.52    inference(cnf_transformation,[],[f13])).
% 1.28/0.52  fof(f37,plain,(
% 1.28/0.52    ( ! [X2,X1] : (k6_relat_1(k2_relat_1(k2_funct_1(X1))) != k5_relat_1(X2,k2_funct_1(X1)) | k1_relat_1(k2_funct_1(X1)) != k2_relat_1(X2) | k2_funct_1(k2_funct_1(X1)) = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(k2_funct_1(X1)) | ~v1_relat_1(k2_funct_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.28/0.52    inference(resolution,[],[f35,f28])).
% 1.28/0.52  fof(f28,plain,(
% 1.28/0.52    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.28/0.52    inference(cnf_transformation,[],[f11])).
% 1.28/0.52  fof(f11,plain,(
% 1.28/0.52    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.28/0.52    inference(flattening,[],[f10])).
% 1.28/0.52  fof(f10,plain,(
% 1.28/0.52    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.28/0.52    inference(ennf_transformation,[],[f2])).
% 1.28/0.52  fof(f2,axiom,(
% 1.28/0.52    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.28/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 1.28/0.52  fof(f35,plain,(
% 1.28/0.52    ( ! [X0,X1] : (~v2_funct_1(X0) | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | k2_funct_1(X0) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.28/0.52    inference(cnf_transformation,[],[f19])).
% 1.28/0.52  fof(f19,plain,(
% 1.28/0.52    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.28/0.52    inference(flattening,[],[f18])).
% 1.28/0.52  fof(f18,plain,(
% 1.28/0.52    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.28/0.52    inference(ennf_transformation,[],[f5])).
% 1.28/0.52  fof(f5,axiom,(
% 1.28/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.28/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 1.28/0.52  % SZS output end Proof for theBenchmark
% 1.28/0.52  % (3486)------------------------------
% 1.28/0.52  % (3486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.52  % (3486)Termination reason: Refutation
% 1.28/0.52  
% 1.28/0.52  % (3486)Memory used [KB]: 6140
% 1.28/0.52  % (3486)Time elapsed: 0.097 s
% 1.28/0.52  % (3486)------------------------------
% 1.28/0.52  % (3486)------------------------------
% 1.28/0.52  % (3466)Success in time 0.166 s
%------------------------------------------------------------------------------
