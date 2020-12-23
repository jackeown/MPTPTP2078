%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 127 expanded)
%              Number of leaves         :   10 (  39 expanded)
%              Depth                    :   19
%              Number of atoms          :  199 ( 601 expanded)
%              Number of equality atoms :  110 ( 321 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f265,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f235,f257])).

fof(f257,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | ~ spl3_1 ),
    inference(trivial_inequality_removal,[],[f255])).

fof(f255,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_1 ),
    inference(superposition,[],[f18,f111])).

fof(f111,plain,
    ( ! [X1] : k1_xboole_0 = X1
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl3_1
  <=> ! [X1] : k1_xboole_0 = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f18,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f11])).

fof(f11,plain,
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

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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

fof(f235,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f214,f136])).

fof(f136,plain,
    ( ! [X0,X1] : X0 = X1
    | ~ spl3_2 ),
    inference(superposition,[],[f114,f114])).

fof(f114,plain,
    ( ! [X0] : k1_setfam_1(k1_setfam_1(k2_relat_1(sK2(sK0)))) = X0
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl3_2
  <=> ! [X0] : k1_setfam_1(k1_setfam_1(k2_relat_1(sK2(sK0)))) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f214,plain,
    ( ! [X0] : k1_xboole_0 != X0
    | ~ spl3_2 ),
    inference(superposition,[],[f18,f136])).

fof(f115,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f90,f113,f110])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k1_setfam_1(k2_relat_1(sK2(sK0)))) = X0
      | k1_xboole_0 = X1 ) ),
    inference(backward_demodulation,[],[f32,f88])).

fof(f88,plain,(
    ! [X8] : k1_setfam_1(k2_relat_1(sK2(sK0))) = X8 ),
    inference(subsumption_resolution,[],[f84,f18])).

fof(f84,plain,(
    ! [X8] :
      ( k1_setfam_1(k2_relat_1(sK2(sK0))) = X8
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f32,f77])).

fof(f77,plain,(
    ! [X0] : sK2(sK0) = sK1(sK0,X0) ),
    inference(subsumption_resolution,[],[f76,f18])).

fof(f76,plain,(
    ! [X0] :
      ( sK2(sK0) = sK1(sK0,X0)
      | k1_xboole_0 = sK0 ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK1(X0,X1) = sK2(sK0)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X4,X2,X3] :
      ( sK0 != X4
      | sK1(X2,X3) = sK2(X4)
      | sK0 != X2
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f45,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK1(X0,X1))
          & k1_relat_1(sK1(X0,X1)) = X0
          & v1_funct_1(sK1(X0,X1))
          & v1_relat_1(sK1(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f13])).

fof(f13,plain,(
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

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f45,plain,(
    ! [X4,X2,X3] :
      ( sK0 != X2
      | sK1(X2,X3) = sK2(X4)
      | sK0 != X4
      | ~ v1_relat_1(sK1(X2,X3))
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f42,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X4,X2,X3] :
      ( sK0 != X2
      | sK1(X2,X3) = sK2(X4)
      | sK0 != X4
      | ~ v1_funct_1(sK1(X2,X3))
      | ~ v1_relat_1(sK1(X2,X3))
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f38,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK1(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != sK0
      | sK2(X0) = X1
      | sK0 != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f37,f25])).

fof(f25,plain,(
    ! [X0] : v1_relat_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X2] :
          ( np__1 = k1_funct_1(sK2(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK2(X0)) = X0
      & v1_funct_1(sK2(X0))
      & v1_relat_1(sK2(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f15])).

fof(f15,plain,(
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

fof(f10,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = np__1 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK2(X0) = X1
      | k1_relat_1(X1) != sK0
      | ~ v1_relat_1(sK2(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f35,f26])).

fof(f26,plain,(
    ! [X0] : v1_funct_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK2(X0) = X1
      | k1_relat_1(X1) != sK0
      | ~ v1_funct_1(sK2(X0))
      | ~ v1_relat_1(sK2(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f17,f27])).

fof(f27,plain,(
    ! [X0] : k1_relat_1(sK2(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f17,plain,(
    ! [X2,X1] :
      ( k1_relat_1(X2) != sK0
      | X1 = X2
      | k1_relat_1(X1) != sK0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_relat_1(sK1(X1,X0))) = X0
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f29,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_relat_1(sK1(X0,X1)) = k2_tarski(X1,X1)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f24,f20])).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f19,f20])).

fof(f19,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:42:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (14138)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (14138)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (14154)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (14146)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f265,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f115,f235,f257])).
% 0.20/0.51  fof(f257,plain,(
% 0.20/0.51    ~spl3_1),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f256])).
% 0.20/0.51  fof(f256,plain,(
% 0.20/0.51    $false | ~spl3_1),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f255])).
% 0.20/0.51  fof(f255,plain,(
% 0.20/0.51    k1_xboole_0 != k1_xboole_0 | ~spl3_1),
% 0.20/0.51    inference(superposition,[],[f18,f111])).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    ( ! [X1] : (k1_xboole_0 = X1) ) | ~spl3_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f110])).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    spl3_1 <=> ! [X1] : k1_xboole_0 = X1),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    k1_xboole_0 != sK0),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f8,plain,(
% 0.20/0.51    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.51    inference(flattening,[],[f7])).
% 0.20/0.51  fof(f7,plain,(
% 0.20/0.51    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,negated_conjecture,(
% 0.20/0.51    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.20/0.51    inference(negated_conjecture,[],[f5])).
% 0.20/0.51  fof(f5,conjecture,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).
% 0.20/0.51  fof(f235,plain,(
% 0.20/0.51    ~spl3_2),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f234])).
% 0.20/0.51  fof(f234,plain,(
% 0.20/0.51    $false | ~spl3_2),
% 0.20/0.51    inference(subsumption_resolution,[],[f214,f136])).
% 0.20/0.51  fof(f136,plain,(
% 0.20/0.51    ( ! [X0,X1] : (X0 = X1) ) | ~spl3_2),
% 0.20/0.51    inference(superposition,[],[f114,f114])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    ( ! [X0] : (k1_setfam_1(k1_setfam_1(k2_relat_1(sK2(sK0)))) = X0) ) | ~spl3_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f113])).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    spl3_2 <=> ! [X0] : k1_setfam_1(k1_setfam_1(k2_relat_1(sK2(sK0)))) = X0),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.51  fof(f214,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 != X0) ) | ~spl3_2),
% 0.20/0.51    inference(superposition,[],[f18,f136])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    spl3_1 | spl3_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f90,f113,f110])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_setfam_1(k1_setfam_1(k2_relat_1(sK2(sK0)))) = X0 | k1_xboole_0 = X1) )),
% 0.20/0.51    inference(backward_demodulation,[],[f32,f88])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    ( ! [X8] : (k1_setfam_1(k2_relat_1(sK2(sK0))) = X8) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f84,f18])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    ( ! [X8] : (k1_setfam_1(k2_relat_1(sK2(sK0))) = X8 | k1_xboole_0 = sK0) )),
% 0.20/0.51    inference(superposition,[],[f32,f77])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    ( ! [X0] : (sK2(sK0) = sK1(sK0,X0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f76,f18])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    ( ! [X0] : (sK2(sK0) = sK1(sK0,X0) | k1_xboole_0 = sK0) )),
% 0.20/0.51    inference(equality_resolution,[],[f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X0,X1] : (sK0 != X0 | sK1(X0,X1) = sK2(sK0) | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(equality_resolution,[],[f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X4,X2,X3] : (sK0 != X4 | sK1(X2,X3) = sK2(X4) | sK0 != X2 | k1_xboole_0 = X2) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f45,f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(sK1(X0,X1)) | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK1(X0,X1)) & k1_relat_1(sK1(X0,X1)) = X0 & v1_funct_1(sK1(X0,X1)) & v1_relat_1(sK1(X0,X1))) | k1_xboole_0 = X0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK1(X0,X1)) & k1_relat_1(sK1(X0,X1)) = X0 & v1_funct_1(sK1(X0,X1)) & v1_relat_1(sK1(X0,X1))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X4,X2,X3] : (sK0 != X2 | sK1(X2,X3) = sK2(X4) | sK0 != X4 | ~v1_relat_1(sK1(X2,X3)) | k1_xboole_0 = X2) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f42,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_funct_1(sK1(X0,X1)) | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X4,X2,X3] : (sK0 != X2 | sK1(X2,X3) = sK2(X4) | sK0 != X4 | ~v1_funct_1(sK1(X2,X3)) | ~v1_relat_1(sK1(X2,X3)) | k1_xboole_0 = X2) )),
% 0.20/0.51    inference(superposition,[],[f38,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_relat_1(sK1(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_relat_1(X1) != sK0 | sK2(X0) = X1 | sK0 != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f37,f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ( ! [X0] : (v1_relat_1(sK2(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0] : (! [X2] : (np__1 = k1_funct_1(sK2(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK2(X0)) = X0 & v1_funct_1(sK2(X0)) & v1_relat_1(sK2(X0)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0] : (? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (np__1 = k1_funct_1(sK2(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK2(X0)) = X0 & v1_funct_1(sK2(X0)) & v1_relat_1(sK2(X0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = np__1) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0,X1] : (sK0 != X0 | sK2(X0) = X1 | k1_relat_1(X1) != sK0 | ~v1_relat_1(sK2(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f35,f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X0] : (v1_funct_1(sK2(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0,X1] : (sK0 != X0 | sK2(X0) = X1 | k1_relat_1(X1) != sK0 | ~v1_funct_1(sK2(X0)) | ~v1_relat_1(sK2(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(superposition,[],[f17,f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X0] : (k1_relat_1(sK2(X0)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ( ! [X2,X1] : (k1_relat_1(X2) != sK0 | X1 = X2 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_setfam_1(k2_relat_1(sK1(X1,X0))) = X0 | k1_xboole_0 = X1) )),
% 0.20/0.51    inference(superposition,[],[f29,f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_relat_1(sK1(X0,X1)) = k2_tarski(X1,X1) | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(definition_unfolding,[],[f24,f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK1(X0,X1)) | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 0.20/0.51    inference(definition_unfolding,[],[f19,f20])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (14138)------------------------------
% 0.20/0.51  % (14138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (14138)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (14138)Memory used [KB]: 10746
% 0.20/0.51  % (14138)Time elapsed: 0.091 s
% 0.20/0.51  % (14138)------------------------------
% 0.20/0.51  % (14138)------------------------------
% 0.20/0.51  % (14137)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (14131)Success in time 0.153 s
%------------------------------------------------------------------------------
