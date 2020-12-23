%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:55 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 315 expanded)
%              Number of leaves         :   10 (  90 expanded)
%              Depth                    :   21
%              Number of atoms          :  193 (1621 expanded)
%              Number of equality atoms :  112 ( 870 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1353,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f24,f314])).

fof(f314,plain,(
    ! [X2,X1] : X1 = X2 ),
    inference(superposition,[],[f109,f109])).

fof(f109,plain,(
    ! [X2,X3] : k1_setfam_1(k1_tarski(X3)) = X2 ),
    inference(superposition,[],[f52,f90])).

fof(f90,plain,(
    ! [X0,X1] : k1_tarski(X0) = k1_tarski(X1) ),
    inference(superposition,[],[f86,f86])).

fof(f86,plain,(
    ! [X3] : k1_tarski(X3) = k2_relat_1(sK2(sK0)) ),
    inference(subsumption_resolution,[],[f81,f24])).

fof(f81,plain,(
    ! [X3] :
      ( k1_tarski(X3) = k2_relat_1(sK2(sK0))
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f29,f73])).

fof(f73,plain,(
    ! [X0] : sK2(sK0) = sK1(sK0,X0) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( sK0 != X1
      | sK2(X1) = sK1(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f66,f24])).

fof(f66,plain,(
    ! [X0,X1] :
      ( sK2(X1) = sK1(sK0,X0)
      | sK0 != X1
      | k1_xboole_0 = sK0 ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X0
      | sK1(X0,X1) = sK2(X2)
      | sK0 != X2
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X0
      | sK1(X0,X1) = sK2(X2)
      | sK0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f50,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK1(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK1(X0,X1))
          & k1_relat_1(sK1(X0,X1)) = X0
          & v1_funct_1(sK1(X0,X1))
          & v1_relat_1(sK1(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_tarski(X1) = k2_relat_1(sK1(X0,X1))
        & k1_relat_1(sK1(X0,X1)) = X0
        & v1_funct_1(sK1(X0,X1))
        & v1_relat_1(sK1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f50,plain,(
    ! [X4,X2,X3] :
      ( sK0 != k1_relat_1(sK1(X2,X3))
      | sK1(X2,X3) = sK2(X4)
      | sK0 != X4
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f48,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X4,X2,X3] :
      ( sK0 != k1_relat_1(sK1(X2,X3))
      | sK1(X2,X3) = sK2(X4)
      | sK0 != X4
      | ~ v1_relat_1(sK1(X2,X3))
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f43,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k1_relat_1(X1) != sK0
      | sK2(X0) = X1
      | sK0 != X0
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f42,f32])).

fof(f32,plain,(
    ! [X0] : k1_relat_1(sK2(X0)) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_relat_1(sK2(X0)) = X0
      & v1_funct_1(sK2(X0))
      & v1_relat_1(sK2(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( k1_relat_1(sK2(X0)) = X0
        & v1_funct_1(sK2(X0))
        & v1_relat_1(sK2(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0] :
    ? [X1] :
      ( k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = k1_xboole_0 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( sK0 != k1_relat_1(sK2(X0))
      | k1_relat_1(X1) != sK0
      | sK2(X0) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f41,f30])).

fof(f30,plain,(
    ! [X0] : v1_relat_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X0,X1] :
      ( sK0 != k1_relat_1(sK2(X0))
      | k1_relat_1(X1) != sK0
      | sK2(X0) = X1
      | ~ v1_relat_1(sK2(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f31,f23])).

fof(f23,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | k1_relat_1(X2) != sK0
      | k1_relat_1(X1) != sK0
      | X1 = X2
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f15])).

fof(f15,plain,
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

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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

fof(f31,plain,(
    ! [X0] : v1_funct_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(backward_demodulation,[],[f46,f51])).

fof(f51,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f35,f39])).

fof(f39,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f46,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k1_setfam_1(k1_tarski(X0)) ),
    inference(superposition,[],[f33,f25])).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f24,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:15:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (14321)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (14314)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (14337)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (14322)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.26/0.53  % (14317)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.26/0.54  % (14319)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.26/0.54  % (14330)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.26/0.54  % (14333)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.26/0.54  % (14330)Refutation not found, incomplete strategy% (14330)------------------------------
% 1.26/0.54  % (14330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.54  % (14330)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.54  
% 1.26/0.54  % (14330)Memory used [KB]: 10618
% 1.26/0.54  % (14330)Time elapsed: 0.128 s
% 1.26/0.54  % (14330)------------------------------
% 1.26/0.54  % (14330)------------------------------
% 1.26/0.54  % (14323)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.26/0.55  % (14332)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.26/0.55  % (14332)Refutation not found, incomplete strategy% (14332)------------------------------
% 1.26/0.55  % (14332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.55  % (14332)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.55  
% 1.26/0.55  % (14332)Memory used [KB]: 1663
% 1.26/0.55  % (14332)Time elapsed: 0.137 s
% 1.26/0.55  % (14332)------------------------------
% 1.26/0.55  % (14332)------------------------------
% 1.26/0.55  % (14336)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.26/0.55  % (14341)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.26/0.55  % (14343)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.26/0.55  % (14341)Refutation not found, incomplete strategy% (14341)------------------------------
% 1.26/0.55  % (14341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.55  % (14341)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.55  
% 1.26/0.55  % (14341)Memory used [KB]: 6140
% 1.26/0.55  % (14341)Time elapsed: 0.138 s
% 1.26/0.55  % (14341)------------------------------
% 1.26/0.55  % (14341)------------------------------
% 1.26/0.55  % (14342)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.52/0.55  % (14324)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.52/0.55  % (14339)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.52/0.55  % (14335)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.52/0.55  % (14339)Refutation not found, incomplete strategy% (14339)------------------------------
% 1.52/0.55  % (14339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.55  % (14339)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.55  
% 1.52/0.55  % (14339)Memory used [KB]: 6140
% 1.52/0.55  % (14339)Time elapsed: 0.146 s
% 1.52/0.55  % (14339)------------------------------
% 1.52/0.55  % (14339)------------------------------
% 1.52/0.56  % (14315)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.52/0.56  % (14321)Refutation found. Thanks to Tanya!
% 1.52/0.56  % SZS status Theorem for theBenchmark
% 1.52/0.56  % (14315)Refutation not found, incomplete strategy% (14315)------------------------------
% 1.52/0.56  % (14315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (14315)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (14315)Memory used [KB]: 1663
% 1.52/0.56  % (14315)Time elapsed: 0.142 s
% 1.52/0.56  % (14315)------------------------------
% 1.52/0.56  % (14315)------------------------------
% 1.52/0.56  % (14340)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.52/0.56  % (14340)Refutation not found, incomplete strategy% (14340)------------------------------
% 1.52/0.56  % (14340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (14340)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (14340)Memory used [KB]: 6140
% 1.52/0.56  % (14340)Time elapsed: 0.144 s
% 1.52/0.56  % (14340)------------------------------
% 1.52/0.56  % (14340)------------------------------
% 1.52/0.56  % (14326)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.52/0.56  % (14318)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.52/0.56  % (14316)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.52/0.56  % (14338)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.52/0.56  % (14325)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.52/0.56  % (14320)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.52/0.56  % (14327)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.52/0.56  % (14331)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.52/0.56  % (14325)Refutation not found, incomplete strategy% (14325)------------------------------
% 1.52/0.56  % (14325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (14325)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (14325)Memory used [KB]: 6268
% 1.52/0.56  % (14325)Time elapsed: 0.160 s
% 1.52/0.56  % (14325)------------------------------
% 1.52/0.56  % (14325)------------------------------
% 1.52/0.56  % (14338)Refutation not found, incomplete strategy% (14338)------------------------------
% 1.52/0.56  % (14338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (14338)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (14338)Memory used [KB]: 10746
% 1.52/0.56  % (14338)Time elapsed: 0.149 s
% 1.52/0.56  % (14338)------------------------------
% 1.52/0.56  % (14338)------------------------------
% 1.52/0.56  % (14331)Refutation not found, incomplete strategy% (14331)------------------------------
% 1.52/0.56  % (14331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (14331)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (14331)Memory used [KB]: 1791
% 1.52/0.56  % (14331)Time elapsed: 0.159 s
% 1.52/0.56  % (14331)------------------------------
% 1.52/0.56  % (14331)------------------------------
% 1.52/0.56  % SZS output start Proof for theBenchmark
% 1.52/0.56  fof(f1353,plain,(
% 1.52/0.56    $false),
% 1.52/0.56    inference(unit_resulting_resolution,[],[f24,f314])).
% 1.52/0.56  fof(f314,plain,(
% 1.52/0.56    ( ! [X2,X1] : (X1 = X2) )),
% 1.52/0.56    inference(superposition,[],[f109,f109])).
% 1.52/0.56  fof(f109,plain,(
% 1.52/0.56    ( ! [X2,X3] : (k1_setfam_1(k1_tarski(X3)) = X2) )),
% 1.52/0.56    inference(superposition,[],[f52,f90])).
% 1.52/0.56  fof(f90,plain,(
% 1.52/0.56    ( ! [X0,X1] : (k1_tarski(X0) = k1_tarski(X1)) )),
% 1.52/0.56    inference(superposition,[],[f86,f86])).
% 1.52/0.56  fof(f86,plain,(
% 1.52/0.56    ( ! [X3] : (k1_tarski(X3) = k2_relat_1(sK2(sK0))) )),
% 1.52/0.56    inference(subsumption_resolution,[],[f81,f24])).
% 1.52/0.56  fof(f81,plain,(
% 1.52/0.56    ( ! [X3] : (k1_tarski(X3) = k2_relat_1(sK2(sK0)) | k1_xboole_0 = sK0) )),
% 1.52/0.56    inference(superposition,[],[f29,f73])).
% 1.52/0.56  fof(f73,plain,(
% 1.52/0.56    ( ! [X0] : (sK2(sK0) = sK1(sK0,X0)) )),
% 1.52/0.56    inference(equality_resolution,[],[f67])).
% 1.52/0.56  fof(f67,plain,(
% 1.52/0.56    ( ! [X0,X1] : (sK0 != X1 | sK2(X1) = sK1(sK0,X0)) )),
% 1.52/0.56    inference(subsumption_resolution,[],[f66,f24])).
% 1.52/0.56  fof(f66,plain,(
% 1.52/0.56    ( ! [X0,X1] : (sK2(X1) = sK1(sK0,X0) | sK0 != X1 | k1_xboole_0 = sK0) )),
% 1.52/0.56    inference(equality_resolution,[],[f60])).
% 1.52/0.56  fof(f60,plain,(
% 1.52/0.56    ( ! [X2,X0,X1] : (sK0 != X0 | sK1(X0,X1) = sK2(X2) | sK0 != X2 | k1_xboole_0 = X0) )),
% 1.52/0.56    inference(duplicate_literal_removal,[],[f59])).
% 1.52/0.56  fof(f59,plain,(
% 1.52/0.56    ( ! [X2,X0,X1] : (sK0 != X0 | sK1(X0,X1) = sK2(X2) | sK0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 = X0) )),
% 1.52/0.56    inference(superposition,[],[f50,f28])).
% 1.52/0.56  fof(f28,plain,(
% 1.52/0.56    ( ! [X0,X1] : (k1_relat_1(sK1(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 1.52/0.56    inference(cnf_transformation,[],[f18])).
% 1.52/0.56  fof(f18,plain,(
% 1.52/0.56    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK1(X0,X1)) & k1_relat_1(sK1(X0,X1)) = X0 & v1_funct_1(sK1(X0,X1)) & v1_relat_1(sK1(X0,X1))) | k1_xboole_0 = X0)),
% 1.52/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f17])).
% 1.52/0.56  fof(f17,plain,(
% 1.52/0.56    ! [X1,X0] : (? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK1(X0,X1)) & k1_relat_1(sK1(X0,X1)) = X0 & v1_funct_1(sK1(X0,X1)) & v1_relat_1(sK1(X0,X1))))),
% 1.52/0.56    introduced(choice_axiom,[])).
% 1.52/0.56  fof(f13,plain,(
% 1.52/0.56    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 1.52/0.56    inference(ennf_transformation,[],[f7])).
% 1.52/0.56  fof(f7,axiom,(
% 1.52/0.56    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 1.52/0.56  fof(f50,plain,(
% 1.52/0.56    ( ! [X4,X2,X3] : (sK0 != k1_relat_1(sK1(X2,X3)) | sK1(X2,X3) = sK2(X4) | sK0 != X4 | k1_xboole_0 = X2) )),
% 1.52/0.56    inference(subsumption_resolution,[],[f48,f26])).
% 1.52/0.56  fof(f26,plain,(
% 1.52/0.56    ( ! [X0,X1] : (v1_relat_1(sK1(X0,X1)) | k1_xboole_0 = X0) )),
% 1.52/0.56    inference(cnf_transformation,[],[f18])).
% 1.52/0.56  fof(f48,plain,(
% 1.52/0.56    ( ! [X4,X2,X3] : (sK0 != k1_relat_1(sK1(X2,X3)) | sK1(X2,X3) = sK2(X4) | sK0 != X4 | ~v1_relat_1(sK1(X2,X3)) | k1_xboole_0 = X2) )),
% 1.52/0.56    inference(resolution,[],[f43,f27])).
% 1.52/0.56  fof(f27,plain,(
% 1.52/0.56    ( ! [X0,X1] : (v1_funct_1(sK1(X0,X1)) | k1_xboole_0 = X0) )),
% 1.52/0.56    inference(cnf_transformation,[],[f18])).
% 1.52/0.56  fof(f43,plain,(
% 1.52/0.56    ( ! [X0,X1] : (~v1_funct_1(X1) | k1_relat_1(X1) != sK0 | sK2(X0) = X1 | sK0 != X0 | ~v1_relat_1(X1)) )),
% 1.52/0.56    inference(forward_demodulation,[],[f42,f32])).
% 1.52/0.56  fof(f32,plain,(
% 1.52/0.56    ( ! [X0] : (k1_relat_1(sK2(X0)) = X0) )),
% 1.52/0.56    inference(cnf_transformation,[],[f20])).
% 1.52/0.56  fof(f20,plain,(
% 1.52/0.56    ! [X0] : (k1_relat_1(sK2(X0)) = X0 & v1_funct_1(sK2(X0)) & v1_relat_1(sK2(X0)))),
% 1.52/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f19])).
% 1.52/0.56  fof(f19,plain,(
% 1.52/0.56    ! [X0] : (? [X1] : (k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(sK2(X0)) = X0 & v1_funct_1(sK2(X0)) & v1_relat_1(sK2(X0))))),
% 1.52/0.56    introduced(choice_axiom,[])).
% 1.52/0.56  fof(f10,plain,(
% 1.52/0.56    ! [X0] : ? [X1] : (k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.52/0.56    inference(pure_predicate_removal,[],[f6])).
% 1.52/0.56  fof(f6,axiom,(
% 1.52/0.56    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = k1_xboole_0) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 1.52/0.56  fof(f42,plain,(
% 1.52/0.56    ( ! [X0,X1] : (sK0 != k1_relat_1(sK2(X0)) | k1_relat_1(X1) != sK0 | sK2(X0) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.52/0.56    inference(subsumption_resolution,[],[f41,f30])).
% 1.52/0.56  fof(f30,plain,(
% 1.52/0.56    ( ! [X0] : (v1_relat_1(sK2(X0))) )),
% 1.52/0.56    inference(cnf_transformation,[],[f20])).
% 1.52/0.56  fof(f41,plain,(
% 1.52/0.56    ( ! [X0,X1] : (sK0 != k1_relat_1(sK2(X0)) | k1_relat_1(X1) != sK0 | sK2(X0) = X1 | ~v1_relat_1(sK2(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.52/0.56    inference(resolution,[],[f31,f23])).
% 1.52/0.56  fof(f23,plain,(
% 1.52/0.56    ( ! [X2,X1] : (~v1_funct_1(X2) | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | X1 = X2 | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f16])).
% 1.52/0.56  fof(f16,plain,(
% 1.52/0.56    k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.52/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f15])).
% 1.52/0.56  fof(f15,plain,(
% 1.52/0.56    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.52/0.56    introduced(choice_axiom,[])).
% 1.52/0.56  fof(f12,plain,(
% 1.52/0.56    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.52/0.56    inference(flattening,[],[f11])).
% 1.52/0.56  fof(f11,plain,(
% 1.52/0.56    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 1.52/0.56    inference(ennf_transformation,[],[f9])).
% 1.52/0.56  fof(f9,negated_conjecture,(
% 1.52/0.56    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 1.52/0.56    inference(negated_conjecture,[],[f8])).
% 1.52/0.56  fof(f8,conjecture,(
% 1.52/0.56    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).
% 1.52/0.56  fof(f31,plain,(
% 1.52/0.56    ( ! [X0] : (v1_funct_1(sK2(X0))) )),
% 1.52/0.56    inference(cnf_transformation,[],[f20])).
% 1.52/0.56  fof(f29,plain,(
% 1.52/0.56    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK1(X0,X1)) | k1_xboole_0 = X0) )),
% 1.52/0.56    inference(cnf_transformation,[],[f18])).
% 1.52/0.56  fof(f52,plain,(
% 1.52/0.56    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 1.52/0.56    inference(backward_demodulation,[],[f46,f51])).
% 1.52/0.56  fof(f51,plain,(
% 1.52/0.56    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.52/0.56    inference(resolution,[],[f35,f39])).
% 1.52/0.56  fof(f39,plain,(
% 1.52/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.52/0.56    inference(equality_resolution,[],[f37])).
% 1.52/0.56  fof(f37,plain,(
% 1.52/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.52/0.56    inference(cnf_transformation,[],[f22])).
% 1.52/0.56  fof(f22,plain,(
% 1.52/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.52/0.56    inference(flattening,[],[f21])).
% 1.52/0.56  fof(f21,plain,(
% 1.52/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.52/0.56    inference(nnf_transformation,[],[f1])).
% 1.52/0.56  fof(f1,axiom,(
% 1.52/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.52/0.56  fof(f35,plain,(
% 1.52/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.52/0.56    inference(cnf_transformation,[],[f14])).
% 1.52/0.56  fof(f14,plain,(
% 1.52/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.52/0.56    inference(ennf_transformation,[],[f2])).
% 1.52/0.56  fof(f2,axiom,(
% 1.52/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.52/0.56  fof(f46,plain,(
% 1.52/0.56    ( ! [X0] : (k3_xboole_0(X0,X0) = k1_setfam_1(k1_tarski(X0))) )),
% 1.52/0.56    inference(superposition,[],[f33,f25])).
% 1.52/0.56  fof(f25,plain,(
% 1.52/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f3])).
% 1.52/0.56  fof(f3,axiom,(
% 1.52/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.52/0.56  fof(f33,plain,(
% 1.52/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.52/0.56    inference(cnf_transformation,[],[f5])).
% 1.52/0.56  fof(f5,axiom,(
% 1.52/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.52/0.56  fof(f24,plain,(
% 1.52/0.56    k1_xboole_0 != sK0),
% 1.52/0.56    inference(cnf_transformation,[],[f16])).
% 1.52/0.56  % SZS output end Proof for theBenchmark
% 1.52/0.56  % (14321)------------------------------
% 1.52/0.56  % (14321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (14321)Termination reason: Refutation
% 1.52/0.56  
% 1.52/0.56  % (14321)Memory used [KB]: 2046
% 1.52/0.56  % (14321)Time elapsed: 0.145 s
% 1.52/0.56  % (14321)------------------------------
% 1.52/0.56  % (14321)------------------------------
% 1.52/0.56  % (14313)Success in time 0.194 s
%------------------------------------------------------------------------------
