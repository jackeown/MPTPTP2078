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
% DateTime   : Thu Dec  3 12:52:00 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 682 expanded)
%              Number of leaves         :   14 ( 211 expanded)
%              Depth                    :   20
%              Number of atoms          :  216 (2697 expanded)
%              Number of equality atoms :  129 (1549 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f242,plain,(
    $false ),
    inference(global_subsumption,[],[f240,f176])).

fof(f176,plain,(
    ! [X1] : ~ r1_xboole_0(X1,X1) ),
    inference(superposition,[],[f50,f114])).

fof(f114,plain,(
    ! [X0,X1] : X0 = X1 ),
    inference(superposition,[],[f105,f105])).

fof(f105,plain,(
    ! [X1] : k1_setfam_1(k2_relat_1(sK2(sK0))) = X1 ),
    inference(subsumption_resolution,[],[f99,f26])).

fof(f26,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f18])).

fof(f18,plain,
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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

fof(f99,plain,(
    ! [X1] :
      ( k1_setfam_1(k2_relat_1(sK2(sK0))) = X1
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f63,f97])).

fof(f97,plain,(
    ! [X0] : sK2(sK0) = sK1(sK0,X0) ),
    inference(subsumption_resolution,[],[f96,f26])).

fof(f96,plain,(
    ! [X0] :
      ( sK2(sK0) = sK1(sK0,X0)
      | k1_xboole_0 = sK0 ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK1(X0,X1) = sK2(sK0)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X4,X2,X3] :
      ( sK0 != X4
      | sK1(X2,X3) = sK2(X4)
      | sK0 != X2
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f89,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK1(X0,X1))
          & k1_relat_1(sK1(X0,X1)) = X0
          & v1_funct_1(sK1(X0,X1))
          & v1_relat_1(sK1(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f20])).

fof(f20,plain,(
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

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f89,plain,(
    ! [X4,X2,X3] :
      ( sK0 != X2
      | sK1(X2,X3) = sK2(X4)
      | sK0 != X4
      | ~ v1_relat_1(sK1(X2,X3))
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f86,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f86,plain,(
    ! [X4,X2,X3] :
      ( sK0 != X2
      | sK1(X2,X3) = sK2(X4)
      | sK0 != X4
      | ~ v1_funct_1(sK1(X2,X3))
      | ~ v1_relat_1(sK1(X2,X3))
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f82,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK1(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != sK0
      | sK2(X0) = X1
      | sK0 != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f81,f34])).

fof(f34,plain,(
    ! [X0] : v1_relat_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X2] :
          ( np__1 = k1_funct_1(sK2(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK2(X0)) = X0
      & v1_funct_1(sK2(X0))
      & v1_relat_1(sK2(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_funct_1(X1,X2) = np__1
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( np__1 = k1_funct_1(sK2(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK2(X0)) = X0
        & v1_funct_1(sK2(X0))
        & v1_relat_1(sK2(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = np__1 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK2(X0) = X1
      | k1_relat_1(X1) != sK0
      | ~ v1_relat_1(sK2(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f79,f35])).

fof(f35,plain,(
    ! [X0] : v1_funct_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f79,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK2(X0) = X1
      | k1_relat_1(X1) != sK0
      | ~ v1_funct_1(sK2(X0))
      | ~ v1_relat_1(sK2(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f25,f36])).

fof(f36,plain,(
    ! [X0] : k1_relat_1(sK2(X0)) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f25,plain,(
    ! [X2,X1] :
      ( k1_relat_1(X2) != sK0
      | X1 = X2
      | k1_relat_1(X1) != sK0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f63,plain,(
    ! [X4,X3] :
      ( k1_setfam_1(k2_relat_1(sK1(X4,X3))) = X3
      | k1_xboole_0 = X4 ) ),
    inference(forward_demodulation,[],[f62,f28])).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f62,plain,(
    ! [X4,X3] :
      ( k1_setfam_1(k2_relat_1(sK1(X4,X3))) = k4_xboole_0(X3,k1_xboole_0)
      | k1_xboole_0 = X4 ) ),
    inference(forward_demodulation,[],[f61,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f54,f28])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f48,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f27,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f44])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f61,plain,(
    ! [X4,X3] :
      ( k4_xboole_0(X3,k4_xboole_0(X3,X3)) = k1_setfam_1(k2_relat_1(sK1(X4,X3)))
      | k1_xboole_0 = X4 ) ),
    inference(superposition,[],[f48,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_relat_1(sK1(X0,X1)) = k1_enumset1(X1,X1,X1)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f33,f45])).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f39])).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X1] : ~ r1_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f43,f45,f45])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(f240,plain,(
    ! [X1] : r1_xboole_0(X1,X1) ),
    inference(subsumption_resolution,[],[f166,f114])).

fof(f166,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | r1_xboole_0(X1,X1) ) ),
    inference(superposition,[],[f58,f114])).

fof(f58,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f42,f56])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:54:54 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.52  % (16213)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.23/0.52  % (16233)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.23/0.52  % (16213)Refutation not found, incomplete strategy% (16213)------------------------------
% 0.23/0.52  % (16213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (16213)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (16213)Memory used [KB]: 1663
% 0.23/0.52  % (16213)Time elapsed: 0.103 s
% 0.23/0.52  % (16213)------------------------------
% 0.23/0.52  % (16213)------------------------------
% 0.23/0.52  % (16235)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.23/0.52  % (16224)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.23/0.53  % (16223)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.23/0.53  % (16222)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.23/0.53  % (16227)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.23/0.53  % (16226)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.23/0.53  % (16219)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.53  % (16216)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.23/0.53  % (16225)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.23/0.54  % (16219)Refutation found. Thanks to Tanya!
% 0.23/0.54  % SZS status Theorem for theBenchmark
% 0.23/0.54  % SZS output start Proof for theBenchmark
% 0.23/0.54  fof(f242,plain,(
% 0.23/0.54    $false),
% 0.23/0.54    inference(global_subsumption,[],[f240,f176])).
% 0.23/0.54  fof(f176,plain,(
% 0.23/0.54    ( ! [X1] : (~r1_xboole_0(X1,X1)) )),
% 0.23/0.54    inference(superposition,[],[f50,f114])).
% 0.23/0.54  fof(f114,plain,(
% 0.23/0.54    ( ! [X0,X1] : (X0 = X1) )),
% 0.23/0.54    inference(superposition,[],[f105,f105])).
% 0.23/0.54  fof(f105,plain,(
% 0.23/0.54    ( ! [X1] : (k1_setfam_1(k2_relat_1(sK2(sK0))) = X1) )),
% 0.23/0.54    inference(subsumption_resolution,[],[f99,f26])).
% 0.23/0.54  fof(f26,plain,(
% 0.23/0.54    k1_xboole_0 != sK0),
% 0.23/0.54    inference(cnf_transformation,[],[f19])).
% 0.23/0.54  fof(f19,plain,(
% 0.23/0.54    k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.23/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f18])).
% 0.23/0.54  fof(f18,plain,(
% 0.23/0.54    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.23/0.54    introduced(choice_axiom,[])).
% 0.23/0.54  fof(f14,plain,(
% 0.23/0.54    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.23/0.54    inference(flattening,[],[f13])).
% 0.23/0.54  fof(f13,plain,(
% 0.23/0.54    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 0.23/0.54    inference(ennf_transformation,[],[f12])).
% 0.23/0.54  fof(f12,negated_conjecture,(
% 0.23/0.54    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.23/0.54    inference(negated_conjecture,[],[f11])).
% 0.23/0.54  fof(f11,conjecture,(
% 0.23/0.54    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).
% 0.23/0.54  fof(f99,plain,(
% 0.23/0.54    ( ! [X1] : (k1_setfam_1(k2_relat_1(sK2(sK0))) = X1 | k1_xboole_0 = sK0) )),
% 0.23/0.54    inference(superposition,[],[f63,f97])).
% 0.23/0.54  fof(f97,plain,(
% 0.23/0.54    ( ! [X0] : (sK2(sK0) = sK1(sK0,X0)) )),
% 0.23/0.54    inference(subsumption_resolution,[],[f96,f26])).
% 0.23/0.54  fof(f96,plain,(
% 0.23/0.54    ( ! [X0] : (sK2(sK0) = sK1(sK0,X0) | k1_xboole_0 = sK0) )),
% 0.23/0.54    inference(equality_resolution,[],[f95])).
% 0.23/0.54  fof(f95,plain,(
% 0.23/0.54    ( ! [X0,X1] : (sK0 != X0 | sK1(X0,X1) = sK2(sK0) | k1_xboole_0 = X0) )),
% 0.23/0.54    inference(equality_resolution,[],[f90])).
% 0.23/0.54  fof(f90,plain,(
% 0.23/0.54    ( ! [X4,X2,X3] : (sK0 != X4 | sK1(X2,X3) = sK2(X4) | sK0 != X2 | k1_xboole_0 = X2) )),
% 0.23/0.54    inference(subsumption_resolution,[],[f89,f30])).
% 0.23/0.54  fof(f30,plain,(
% 0.23/0.54    ( ! [X0,X1] : (v1_relat_1(sK1(X0,X1)) | k1_xboole_0 = X0) )),
% 0.23/0.54    inference(cnf_transformation,[],[f21])).
% 0.23/0.54  fof(f21,plain,(
% 0.23/0.54    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK1(X0,X1)) & k1_relat_1(sK1(X0,X1)) = X0 & v1_funct_1(sK1(X0,X1)) & v1_relat_1(sK1(X0,X1))) | k1_xboole_0 = X0)),
% 0.23/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f20])).
% 0.23/0.54  fof(f20,plain,(
% 0.23/0.54    ! [X1,X0] : (? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK1(X0,X1)) & k1_relat_1(sK1(X0,X1)) = X0 & v1_funct_1(sK1(X0,X1)) & v1_relat_1(sK1(X0,X1))))),
% 0.23/0.54    introduced(choice_axiom,[])).
% 0.23/0.54  fof(f15,plain,(
% 0.23/0.54    ! [X0] : (! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 0.23/0.54    inference(ennf_transformation,[],[f10])).
% 0.23/0.54  fof(f10,axiom,(
% 0.23/0.54    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 0.23/0.54  fof(f89,plain,(
% 0.23/0.54    ( ! [X4,X2,X3] : (sK0 != X2 | sK1(X2,X3) = sK2(X4) | sK0 != X4 | ~v1_relat_1(sK1(X2,X3)) | k1_xboole_0 = X2) )),
% 0.23/0.54    inference(subsumption_resolution,[],[f86,f31])).
% 0.23/0.54  fof(f31,plain,(
% 0.23/0.54    ( ! [X0,X1] : (v1_funct_1(sK1(X0,X1)) | k1_xboole_0 = X0) )),
% 0.23/0.54    inference(cnf_transformation,[],[f21])).
% 0.23/0.54  fof(f86,plain,(
% 0.23/0.54    ( ! [X4,X2,X3] : (sK0 != X2 | sK1(X2,X3) = sK2(X4) | sK0 != X4 | ~v1_funct_1(sK1(X2,X3)) | ~v1_relat_1(sK1(X2,X3)) | k1_xboole_0 = X2) )),
% 0.23/0.54    inference(superposition,[],[f82,f32])).
% 0.23/0.54  fof(f32,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k1_relat_1(sK1(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 0.23/0.54    inference(cnf_transformation,[],[f21])).
% 0.23/0.54  fof(f82,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k1_relat_1(X1) != sK0 | sK2(X0) = X1 | sK0 != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.23/0.54    inference(subsumption_resolution,[],[f81,f34])).
% 0.23/0.54  fof(f34,plain,(
% 0.23/0.54    ( ! [X0] : (v1_relat_1(sK2(X0))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f23])).
% 0.23/0.54  fof(f23,plain,(
% 0.23/0.54    ! [X0] : (! [X2] : (np__1 = k1_funct_1(sK2(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK2(X0)) = X0 & v1_funct_1(sK2(X0)) & v1_relat_1(sK2(X0)))),
% 0.23/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f22])).
% 0.23/0.54  fof(f22,plain,(
% 0.23/0.54    ! [X0] : (? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (np__1 = k1_funct_1(sK2(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK2(X0)) = X0 & v1_funct_1(sK2(X0)) & v1_relat_1(sK2(X0))))),
% 0.23/0.54    introduced(choice_axiom,[])).
% 0.23/0.54  fof(f16,plain,(
% 0.23/0.54    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.23/0.54    inference(ennf_transformation,[],[f9])).
% 0.23/0.54  fof(f9,axiom,(
% 0.23/0.54    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = np__1) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).
% 0.23/0.54  fof(f81,plain,(
% 0.23/0.54    ( ! [X0,X1] : (sK0 != X0 | sK2(X0) = X1 | k1_relat_1(X1) != sK0 | ~v1_relat_1(sK2(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.23/0.54    inference(subsumption_resolution,[],[f79,f35])).
% 0.23/0.54  fof(f35,plain,(
% 0.23/0.54    ( ! [X0] : (v1_funct_1(sK2(X0))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f23])).
% 0.23/0.54  fof(f79,plain,(
% 0.23/0.54    ( ! [X0,X1] : (sK0 != X0 | sK2(X0) = X1 | k1_relat_1(X1) != sK0 | ~v1_funct_1(sK2(X0)) | ~v1_relat_1(sK2(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.23/0.54    inference(superposition,[],[f25,f36])).
% 0.23/0.54  fof(f36,plain,(
% 0.23/0.54    ( ! [X0] : (k1_relat_1(sK2(X0)) = X0) )),
% 0.23/0.54    inference(cnf_transformation,[],[f23])).
% 0.23/0.54  fof(f25,plain,(
% 0.23/0.54    ( ! [X2,X1] : (k1_relat_1(X2) != sK0 | X1 = X2 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f19])).
% 0.23/0.54  fof(f63,plain,(
% 0.23/0.54    ( ! [X4,X3] : (k1_setfam_1(k2_relat_1(sK1(X4,X3))) = X3 | k1_xboole_0 = X4) )),
% 0.23/0.54    inference(forward_demodulation,[],[f62,f28])).
% 0.23/0.54  fof(f28,plain,(
% 0.23/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.54    inference(cnf_transformation,[],[f2])).
% 0.23/0.54  fof(f2,axiom,(
% 0.23/0.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.23/0.54  fof(f62,plain,(
% 0.23/0.54    ( ! [X4,X3] : (k1_setfam_1(k2_relat_1(sK1(X4,X3))) = k4_xboole_0(X3,k1_xboole_0) | k1_xboole_0 = X4) )),
% 0.23/0.54    inference(forward_demodulation,[],[f61,f56])).
% 0.23/0.54  fof(f56,plain,(
% 0.23/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.23/0.54    inference(forward_demodulation,[],[f54,f28])).
% 0.23/0.54  fof(f54,plain,(
% 0.23/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.23/0.54    inference(superposition,[],[f48,f46])).
% 0.23/0.54  fof(f46,plain,(
% 0.23/0.54    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0))) )),
% 0.23/0.54    inference(definition_unfolding,[],[f27,f44])).
% 0.23/0.54  fof(f44,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.23/0.54    inference(definition_unfolding,[],[f38,f39])).
% 0.23/0.54  fof(f39,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f6])).
% 0.23/0.54  fof(f6,axiom,(
% 0.23/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.23/0.54  fof(f38,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f8])).
% 0.23/0.54  fof(f8,axiom,(
% 0.23/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.23/0.54  fof(f27,plain,(
% 0.23/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f1])).
% 0.23/0.54  fof(f1,axiom,(
% 0.23/0.54    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.23/0.54  fof(f48,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.23/0.54    inference(definition_unfolding,[],[f40,f44])).
% 0.23/0.54  fof(f40,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f3])).
% 0.23/0.54  fof(f3,axiom,(
% 0.23/0.54    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.23/0.54  fof(f61,plain,(
% 0.23/0.54    ( ! [X4,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X3)) = k1_setfam_1(k2_relat_1(sK1(X4,X3))) | k1_xboole_0 = X4) )),
% 0.23/0.54    inference(superposition,[],[f48,f47])).
% 0.23/0.54  fof(f47,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k2_relat_1(sK1(X0,X1)) = k1_enumset1(X1,X1,X1) | k1_xboole_0 = X0) )),
% 0.23/0.54    inference(definition_unfolding,[],[f33,f45])).
% 0.23/0.54  fof(f45,plain,(
% 0.23/0.54    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.23/0.54    inference(definition_unfolding,[],[f29,f39])).
% 0.23/0.54  fof(f29,plain,(
% 0.23/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f5])).
% 0.23/0.54  fof(f5,axiom,(
% 0.23/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.23/0.54  fof(f33,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK1(X0,X1)) | k1_xboole_0 = X0) )),
% 0.23/0.54    inference(cnf_transformation,[],[f21])).
% 0.23/0.54  fof(f50,plain,(
% 0.23/0.54    ( ! [X1] : (~r1_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1))) )),
% 0.23/0.54    inference(equality_resolution,[],[f49])).
% 0.23/0.54  fof(f49,plain,(
% 0.23/0.54    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))) )),
% 0.23/0.54    inference(definition_unfolding,[],[f43,f45,f45])).
% 0.23/0.54  fof(f43,plain,(
% 0.23/0.54    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f17])).
% 0.23/0.54  fof(f17,plain,(
% 0.23/0.54    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.23/0.54    inference(ennf_transformation,[],[f7])).
% 0.23/0.54  fof(f7,axiom,(
% 0.23/0.54    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).
% 0.23/0.54  fof(f240,plain,(
% 0.23/0.54    ( ! [X1] : (r1_xboole_0(X1,X1)) )),
% 0.23/0.54    inference(subsumption_resolution,[],[f166,f114])).
% 0.23/0.54  fof(f166,plain,(
% 0.23/0.54    ( ! [X0,X1] : (X0 != X1 | r1_xboole_0(X1,X1)) )),
% 0.23/0.54    inference(superposition,[],[f58,f114])).
% 0.23/0.54  fof(f58,plain,(
% 0.23/0.54    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 0.23/0.54    inference(superposition,[],[f42,f56])).
% 0.23/0.54  fof(f42,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f24])).
% 0.23/0.54  fof(f24,plain,(
% 0.23/0.54    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.23/0.54    inference(nnf_transformation,[],[f4])).
% 0.23/0.54  fof(f4,axiom,(
% 0.23/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.23/0.54  % SZS output end Proof for theBenchmark
% 0.23/0.54  % (16219)------------------------------
% 0.23/0.54  % (16219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (16219)Termination reason: Refutation
% 0.23/0.54  
% 0.23/0.54  % (16219)Memory used [KB]: 10746
% 0.23/0.54  % (16219)Time elapsed: 0.081 s
% 0.23/0.54  % (16219)------------------------------
% 0.23/0.54  % (16219)------------------------------
% 0.23/0.54  % (16225)Refutation not found, incomplete strategy% (16225)------------------------------
% 0.23/0.54  % (16225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (16225)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (16225)Memory used [KB]: 10618
% 0.23/0.54  % (16225)Time elapsed: 0.120 s
% 0.23/0.54  % (16225)------------------------------
% 0.23/0.54  % (16225)------------------------------
% 0.23/0.54  % (16218)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.54  % (16227)Refutation not found, incomplete strategy% (16227)------------------------------
% 0.23/0.54  % (16227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (16227)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (16227)Memory used [KB]: 1791
% 0.23/0.54  % (16227)Time elapsed: 0.076 s
% 0.23/0.54  % (16227)------------------------------
% 0.23/0.54  % (16227)------------------------------
% 0.23/0.54  % (16211)Success in time 0.174 s
%------------------------------------------------------------------------------
