%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 314 expanded)
%              Number of leaves         :    7 (  76 expanded)
%              Depth                    :   19
%              Number of atoms          :  214 (1240 expanded)
%              Number of equality atoms :   59 ( 308 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f333,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f332])).

fof(f332,plain,(
    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k2_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f331,f39])).

fof(f39,plain,(
    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f24,f28])).

fof(f28,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( sK0 != k2_funct_1(k2_funct_1(sK0))
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f22])).

fof(f22,plain,
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

fof(f10,plain,(
    ? [X0] :
      ( k2_funct_1(k2_funct_1(X0)) != X0
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( k2_funct_1(k2_funct_1(X0)) != X0
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f331,plain,(
    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(k4_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f330,f61])).

fof(f61,plain,(
    v1_relat_1(k4_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f52,f58])).

fof(f58,plain,(
    k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f57,f25])).

fof(f25,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f46,f26])).

fof(f26,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f46,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(resolution,[],[f24,f35])).

fof(f35,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f52,plain,(
    v1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f51,f25])).

fof(f51,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f41,f26])).

fof(f41,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(resolution,[],[f24,f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f330,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(k4_relat_1(sK0)))
    | ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f329,f60])).

fof(f60,plain,(
    v1_funct_1(k4_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f54,f58])).

fof(f54,plain,(
    v1_funct_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f53,f25])).

fof(f53,plain,
    ( v1_funct_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f42,f26])).

fof(f42,plain,
    ( v1_funct_1(k2_funct_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(resolution,[],[f24,f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f329,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(k4_relat_1(sK0)))
    | ~ v1_funct_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f328,f24])).

fof(f328,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(k4_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f327,f25])).

fof(f327,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(k4_relat_1(sK0)))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f326,f59])).

fof(f59,plain,(
    v2_funct_1(k4_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f56,f58])).

fof(f56,plain,(
    v2_funct_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f55,f25])).

fof(f55,plain,
    ( v2_funct_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f43,f26])).

fof(f43,plain,
    ( v2_funct_1(k2_funct_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(resolution,[],[f24,f32])).

fof(f32,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f326,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(k4_relat_1(sK0)))
    | ~ v2_funct_1(k4_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f325,f40])).

fof(f40,plain,(
    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f24,f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f325,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(k4_relat_1(sK0)))
    | k1_relat_1(sK0) != k2_relat_1(k4_relat_1(sK0))
    | ~ v2_funct_1(k4_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f324,f62])).

fof(f62,plain,(
    sK0 != k2_funct_1(k4_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f27,f58])).

fof(f27,plain,(
    sK0 != k2_funct_1(k2_funct_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f324,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(k4_relat_1(sK0)))
    | sK0 = k2_funct_1(k4_relat_1(sK0))
    | k1_relat_1(sK0) != k2_relat_1(k4_relat_1(sK0))
    | ~ v2_funct_1(k4_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(superposition,[],[f38,f68])).

fof(f68,plain,(
    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0) ),
    inference(forward_demodulation,[],[f67,f58])).

fof(f67,plain,(
    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f66,f25])).

fof(f66,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f48,f26])).

fof(f48,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(resolution,[],[f24,f37])).

fof(f37,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:37:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (23462)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.46  % (23462)Refutation not found, incomplete strategy% (23462)------------------------------
% 0.22/0.46  % (23462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (23462)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.46  
% 0.22/0.46  % (23462)Memory used [KB]: 6140
% 0.22/0.46  % (23462)Time elapsed: 0.044 s
% 0.22/0.46  % (23462)------------------------------
% 0.22/0.46  % (23462)------------------------------
% 0.22/0.47  % (23478)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.47  % (23478)Refutation not found, incomplete strategy% (23478)------------------------------
% 0.22/0.47  % (23478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (23478)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (23478)Memory used [KB]: 10618
% 0.22/0.47  % (23478)Time elapsed: 0.056 s
% 0.22/0.47  % (23478)------------------------------
% 0.22/0.47  % (23478)------------------------------
% 0.22/0.48  % (23465)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.49  % (23459)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.49  % (23465)Refutation not found, incomplete strategy% (23465)------------------------------
% 0.22/0.49  % (23465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (23465)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (23465)Memory used [KB]: 10490
% 0.22/0.49  % (23465)Time elapsed: 0.078 s
% 0.22/0.49  % (23465)------------------------------
% 0.22/0.49  % (23465)------------------------------
% 0.22/0.49  % (23456)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.49  % (23477)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.49  % (23473)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.49  % (23457)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.49  % (23474)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.49  % (23461)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.50  % (23460)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.50  % (23469)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.50  % (23466)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.50  % (23467)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.50  % (23466)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f333,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f332])).
% 0.22/0.50  fof(f332,plain,(
% 0.22/0.50    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k2_relat_1(sK0))),
% 0.22/0.50    inference(forward_demodulation,[],[f331,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.22/0.50    inference(resolution,[],[f24,f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    v1_relat_1(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    sK0 != k2_funct_1(k2_funct_1(sK0)) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ? [X0] : (k2_funct_1(k2_funct_1(X0)) != X0 & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (sK0 != k2_funct_1(k2_funct_1(sK0)) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ? [X0] : (k2_funct_1(k2_funct_1(X0)) != X0 & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f9])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ? [X0] : ((k2_funct_1(k2_funct_1(X0)) != X0 & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.22/0.50    inference(negated_conjecture,[],[f7])).
% 0.22/0.50  fof(f7,conjecture,(
% 0.22/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 0.22/0.50  fof(f331,plain,(
% 0.22/0.50    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(k4_relat_1(sK0)))),
% 0.22/0.50    inference(subsumption_resolution,[],[f330,f61])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    v1_relat_1(k4_relat_1(sK0))),
% 0.22/0.50    inference(backward_demodulation,[],[f52,f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f57,f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    v1_funct_1(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    k2_funct_1(sK0) = k4_relat_1(sK0) | ~v1_funct_1(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f46,f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    v2_funct_1(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    k2_funct_1(sK0) = k4_relat_1(sK0) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0)),
% 0.22/0.50    inference(resolution,[],[f24,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    v1_relat_1(k2_funct_1(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f51,f25])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    v1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f41,f26])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    v1_relat_1(k2_funct_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0)),
% 0.22/0.50    inference(resolution,[],[f24,f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.22/0.50  fof(f330,plain,(
% 0.22/0.50    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(k4_relat_1(sK0))) | ~v1_relat_1(k4_relat_1(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f329,f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    v1_funct_1(k4_relat_1(sK0))),
% 0.22/0.50    inference(backward_demodulation,[],[f54,f58])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    v1_funct_1(k2_funct_1(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f53,f25])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    v1_funct_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f42,f26])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    v1_funct_1(k2_funct_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0)),
% 0.22/0.50    inference(resolution,[],[f24,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f329,plain,(
% 0.22/0.50    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(k4_relat_1(sK0))) | ~v1_funct_1(k4_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f328,f24])).
% 0.22/0.50  fof(f328,plain,(
% 0.22/0.50    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(k4_relat_1(sK0))) | ~v1_relat_1(sK0) | ~v1_funct_1(k4_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f327,f25])).
% 0.22/0.50  fof(f327,plain,(
% 0.22/0.50    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(k4_relat_1(sK0))) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(k4_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f326,f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    v2_funct_1(k4_relat_1(sK0))),
% 0.22/0.50    inference(backward_demodulation,[],[f56,f58])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    v2_funct_1(k2_funct_1(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f55,f25])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    v2_funct_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f43,f26])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    v2_funct_1(k2_funct_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0)),
% 0.22/0.50    inference(resolution,[],[f24,f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f326,plain,(
% 0.22/0.50    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(k4_relat_1(sK0))) | ~v2_funct_1(k4_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(k4_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f325,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))),
% 0.22/0.50    inference(resolution,[],[f24,f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f325,plain,(
% 0.22/0.50    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(k4_relat_1(sK0))) | k1_relat_1(sK0) != k2_relat_1(k4_relat_1(sK0)) | ~v2_funct_1(k4_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(k4_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f324,f62])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    sK0 != k2_funct_1(k4_relat_1(sK0))),
% 0.22/0.50    inference(backward_demodulation,[],[f27,f58])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    sK0 != k2_funct_1(k2_funct_1(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f324,plain,(
% 0.22/0.50    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(k4_relat_1(sK0))) | sK0 = k2_funct_1(k4_relat_1(sK0)) | k1_relat_1(sK0) != k2_relat_1(k4_relat_1(sK0)) | ~v2_funct_1(k4_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(k4_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0))),
% 0.22/0.50    inference(superposition,[],[f38,f68])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),sK0)),
% 0.22/0.50    inference(forward_demodulation,[],[f67,f58])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f66,f25])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) | ~v1_funct_1(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f48,f26])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0)),
% 0.22/0.50    inference(resolution,[],[f24,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (23466)------------------------------
% 0.22/0.50  % (23466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (23466)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (23466)Memory used [KB]: 1663
% 0.22/0.50  % (23466)Time elapsed: 0.088 s
% 0.22/0.50  % (23466)------------------------------
% 0.22/0.50  % (23466)------------------------------
% 0.22/0.50  % (23454)Success in time 0.142 s
%------------------------------------------------------------------------------
