%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 654 expanded)
%              Number of leaves         :   10 ( 189 expanded)
%              Depth                    :   24
%              Number of atoms          :  192 (3778 expanded)
%              Number of equality atoms :  122 (2135 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (32482)Refutation not found, incomplete strategy% (32482)------------------------------
% (32482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (32482)Termination reason: Refutation not found, incomplete strategy

% (32482)Memory used [KB]: 10490
% (32482)Time elapsed: 0.113 s
% (32482)------------------------------
% (32482)------------------------------
fof(f314,plain,(
    $false ),
    inference(subsumption_resolution,[],[f184,f164])).

fof(f164,plain,(
    ! [X0,X1] : X0 = X1 ),
    inference(subsumption_resolution,[],[f160,f121])).

fof(f121,plain,(
    ! [X5] : k1_xboole_0 != k1_tarski(X5) ),
    inference(superposition,[],[f98,f64])).

fof(f64,plain,(
    ! [X6,X7] : k1_tarski(X6) = k2_relat_1(sK1(sK0,X7)) ),
    inference(subsumption_resolution,[],[f59,f29])).

fof(f29,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k1_xboole_0 != sK0
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK0
            | k1_relat_1(X1) != sK0
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k1_relat_1(X2) != X0
                | k1_relat_1(X1) != X0
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
   => ( k1_xboole_0 != sK0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK0
              | k1_relat_1(X1) != sK0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k1_relat_1(X2) = X0
                    & k1_relat_1(X1) = X0 )
                 => X1 = X2 ) ) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).

fof(f59,plain,(
    ! [X6,X7] :
      ( k1_tarski(X6) = k2_relat_1(sK1(sK0,X7))
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f34,f51])).

fof(f51,plain,(
    ! [X0,X1] : sK1(sK0,X0) = sK1(sK0,X1) ),
    inference(subsumption_resolution,[],[f50,f29])).

fof(f50,plain,(
    ! [X0,X1] :
      ( sK1(sK0,X0) = sK1(sK0,X1)
      | k1_xboole_0 = sK0 ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X0
      | sK1(X0,X1) = sK1(sK0,X2)
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f48,f29])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( sK1(X0,X1) = sK1(sK0,X2)
      | sK0 != X0
      | k1_xboole_0 = sK0
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( sK0 != X2
      | sK1(X0,X1) = sK1(X2,X3)
      | sK0 != X0
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f46,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK1(X0,X1))
          & k1_relat_1(sK1(X0,X1)) = X0
          & v1_funct_1(sK1(X0,X1))
          & v1_relat_1(sK1(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_tarski(X1) = k2_relat_1(sK1(X0,X1))
        & k1_relat_1(sK1(X0,X1)) = X0
        & v1_funct_1(sK1(X0,X1))
        & v1_relat_1(sK1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( sK0 != X0
      | sK1(X0,X1) = sK1(X2,X3)
      | sK0 != X2
      | ~ v1_relat_1(sK1(X0,X1))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f45,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( sK0 != X0
      | sK1(X0,X1) = sK1(X2,X3)
      | sK0 != X2
      | ~ v1_funct_1(sK1(X0,X1))
      | ~ v1_relat_1(sK1(X0,X1))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f44,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK1(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) != sK0
      | sK1(X0,X1) = X2
      | sK0 != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f43,f31])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X0
      | sK1(X0,X1) = X2
      | k1_relat_1(X2) != sK0
      | ~ v1_relat_1(sK1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f42,f32])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X0
      | sK1(X0,X1) = X2
      | k1_relat_1(X2) != sK0
      | ~ v1_funct_1(sK1(X0,X1))
      | ~ v1_relat_1(sK1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f28,f33])).

fof(f28,plain,(
    ! [X2,X1] :
      ( k1_relat_1(X2) != sK0
      | X1 = X2
      | k1_relat_1(X1) != sK0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f98,plain,(
    ! [X0] : k1_xboole_0 != k2_relat_1(sK1(sK0,X0)) ),
    inference(superposition,[],[f74,f30])).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f74,plain,(
    ! [X10,X11] : k1_xboole_0 != k2_xboole_0(k2_relat_1(sK1(sK0,X10)),X11) ),
    inference(superposition,[],[f37,f64])).

fof(f37,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f160,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(resolution,[],[f155,f36])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f155,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X3,k1_tarski(X1))
      | X1 = X2 ) ),
    inference(trivial_inequality_removal,[],[f154])).

fof(f154,plain,(
    ! [X2,X3,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | X1 = X2
      | ~ r2_hidden(X3,k1_tarski(X1)) ) ),
    inference(superposition,[],[f73,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k2_relat_1(sK1(sK0,X1)),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(superposition,[],[f41,f64])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f73,plain,(
    ! [X6,X8,X7] :
      ( k1_xboole_0 != k4_xboole_0(k2_relat_1(sK1(sK0,X7)),k1_tarski(X8))
      | X6 = X8 ) ),
    inference(superposition,[],[f39,f64])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

fof(f184,plain,(
    ! [X2] : k1_xboole_0 != X2 ),
    inference(superposition,[],[f37,f164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:47:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (32471)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (32471)Refutation not found, incomplete strategy% (32471)------------------------------
% 0.21/0.51  % (32471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32471)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (32471)Memory used [KB]: 10490
% 0.21/0.51  % (32471)Time elapsed: 0.052 s
% 0.21/0.51  % (32471)------------------------------
% 0.21/0.51  % (32471)------------------------------
% 0.21/0.51  % (32474)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (32477)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (32477)Refutation not found, incomplete strategy% (32477)------------------------------
% 0.21/0.52  % (32477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (32477)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (32477)Memory used [KB]: 10490
% 0.21/0.52  % (32477)Time elapsed: 0.101 s
% 0.21/0.52  % (32477)------------------------------
% 0.21/0.52  % (32477)------------------------------
% 0.21/0.52  % (32492)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (32484)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (32484)Refutation not found, incomplete strategy% (32484)------------------------------
% 0.21/0.52  % (32484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (32484)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (32484)Memory used [KB]: 6012
% 0.21/0.52  % (32484)Time elapsed: 0.100 s
% 0.21/0.52  % (32484)------------------------------
% 0.21/0.52  % (32484)------------------------------
% 0.21/0.52  % (32493)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (32481)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  % (32489)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (32476)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (32490)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.53  % (32473)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (32482)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (32489)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  % (32482)Refutation not found, incomplete strategy% (32482)------------------------------
% 0.21/0.53  % (32482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (32482)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (32482)Memory used [KB]: 10490
% 0.21/0.53  % (32482)Time elapsed: 0.113 s
% 0.21/0.53  % (32482)------------------------------
% 0.21/0.53  % (32482)------------------------------
% 0.21/0.53  fof(f314,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f184,f164])).
% 0.21/0.53  fof(f164,plain,(
% 0.21/0.53    ( ! [X0,X1] : (X0 = X1) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f160,f121])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    ( ! [X5] : (k1_xboole_0 != k1_tarski(X5)) )),
% 0.21/0.53    inference(superposition,[],[f98,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X6,X7] : (k1_tarski(X6) = k2_relat_1(sK1(sK0,X7))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f59,f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    k1_xboole_0 != sK0),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.53    inference(flattening,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.21/0.53    inference(negated_conjecture,[],[f10])).
% 0.21/0.53  fof(f10,conjecture,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X6,X7] : (k1_tarski(X6) = k2_relat_1(sK1(sK0,X7)) | k1_xboole_0 = sK0) )),
% 0.21/0.53    inference(superposition,[],[f34,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sK1(sK0,X0) = sK1(sK0,X1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f50,f29])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sK1(sK0,X0) = sK1(sK0,X1) | k1_xboole_0 = sK0) )),
% 0.21/0.53    inference(equality_resolution,[],[f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (sK0 != X0 | sK1(X0,X1) = sK1(sK0,X2) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f48,f29])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (sK1(X0,X1) = sK1(sK0,X2) | sK0 != X0 | k1_xboole_0 = sK0 | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(equality_resolution,[],[f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (sK0 != X2 | sK1(X0,X1) = sK1(X2,X3) | sK0 != X0 | k1_xboole_0 = X2 | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f46,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_relat_1(sK1(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK1(X0,X1)) & k1_relat_1(sK1(X0,X1)) = X0 & v1_funct_1(sK1(X0,X1)) & v1_relat_1(sK1(X0,X1))) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK1(X0,X1)) & k1_relat_1(sK1(X0,X1)) = X0 & v1_funct_1(sK1(X0,X1)) & v1_relat_1(sK1(X0,X1))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (sK0 != X0 | sK1(X0,X1) = sK1(X2,X3) | sK0 != X2 | ~v1_relat_1(sK1(X0,X1)) | k1_xboole_0 = X2 | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f45,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_funct_1(sK1(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (sK0 != X0 | sK1(X0,X1) = sK1(X2,X3) | sK0 != X2 | ~v1_funct_1(sK1(X0,X1)) | ~v1_relat_1(sK1(X0,X1)) | k1_xboole_0 = X2 | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(superposition,[],[f44,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_relat_1(sK1(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_relat_1(X2) != sK0 | sK1(X0,X1) = X2 | sK0 != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f43,f31])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (sK0 != X0 | sK1(X0,X1) = X2 | k1_relat_1(X2) != sK0 | ~v1_relat_1(sK1(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f42,f32])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (sK0 != X0 | sK1(X0,X1) = X2 | k1_relat_1(X2) != sK0 | ~v1_funct_1(sK1(X0,X1)) | ~v1_relat_1(sK1(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(superposition,[],[f28,f33])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X2,X1] : (k1_relat_1(X2) != sK0 | X1 = X2 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK1(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 != k2_relat_1(sK1(sK0,X0))) )),
% 0.21/0.53    inference(superposition,[],[f74,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X10,X11] : (k1_xboole_0 != k2_xboole_0(k2_relat_1(sK1(sK0,X10)),X11)) )),
% 0.21/0.53    inference(superposition,[],[f37,f64])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.53  fof(f160,plain,(
% 0.21/0.53    ( ! [X0,X1] : (X0 = X1 | k1_xboole_0 = k1_tarski(X0)) )),
% 0.21/0.53    inference(resolution,[],[f155,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.53  fof(f155,plain,(
% 0.21/0.53    ( ! [X2,X3,X1] : (~r2_hidden(X3,k1_tarski(X1)) | X1 = X2) )),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f154])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    ( ! [X2,X3,X1] : (k1_xboole_0 != k1_xboole_0 | X1 = X2 | ~r2_hidden(X3,k1_tarski(X1))) )),
% 0.21/0.53    inference(superposition,[],[f73,f71])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(k2_relat_1(sK1(sK0,X1)),X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.53    inference(superposition,[],[f41,f64])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.53    inference(unused_predicate_definition_removal,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X6,X8,X7] : (k1_xboole_0 != k4_xboole_0(k2_relat_1(sK1(sK0,X7)),k1_tarski(X8)) | X6 = X8) )),
% 0.21/0.53    inference(superposition,[],[f39,f64])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0,X1] : (X0 = X1 | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    ( ! [X2] : (k1_xboole_0 != X2) )),
% 0.21/0.53    inference(superposition,[],[f37,f164])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (32489)------------------------------
% 0.21/0.53  % (32489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (32489)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (32489)Memory used [KB]: 1663
% 0.21/0.53  % (32489)Time elapsed: 0.117 s
% 0.21/0.53  % (32489)------------------------------
% 0.21/0.53  % (32489)------------------------------
% 0.21/0.53  % (32470)Success in time 0.167 s
%------------------------------------------------------------------------------
