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
% DateTime   : Thu Dec  3 12:51:57 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 114 expanded)
%              Number of leaves         :   10 (  28 expanded)
%              Depth                    :   15
%              Number of atoms          :  189 ( 400 expanded)
%              Number of equality atoms :   90 ( 184 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f226,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f156,f208,f225])).

fof(f225,plain,(
    ~ spl8_1 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f223,f21])).

fof(f21,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).

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
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

fof(f223,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_1 ),
    inference(forward_demodulation,[],[f217,f57])).

fof(f57,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f29,f53])).

fof(f53,plain,(
    k1_xboole_0 = sK3(k1_xboole_0) ),
    inference(superposition,[],[f52,f46])).

fof(f46,plain,(
    ! [X0] : sK3(X0) = k7_relat_1(sK3(X0),X0) ),
    inference(forward_demodulation,[],[f44,f29])).

fof(f44,plain,(
    ! [X0] : sK3(X0) = k7_relat_1(sK3(X0),k1_relat_1(sK3(X0))) ),
    inference(resolution,[],[f24,f27])).

fof(f27,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f52,plain,(
    k1_xboole_0 = k7_relat_1(sK3(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f50,f40])).

fof(f40,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k7_relat_1(sK3(X0),X1) ) ),
    inference(forward_demodulation,[],[f48,f29])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(sK3(X0)),X1)
      | k1_xboole_0 = k7_relat_1(sK3(X0),X1) ) ),
    inference(resolution,[],[f30,f27])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f29,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f217,plain,
    ( sK0 = k1_relat_1(k1_xboole_0)
    | ~ spl8_1 ),
    inference(superposition,[],[f29,f152])).

fof(f152,plain,
    ( k1_xboole_0 = sK3(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl8_1
  <=> k1_xboole_0 = sK3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f208,plain,(
    ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f21,f157])).

fof(f157,plain,
    ( ! [X0,X1] : X0 = X1
    | ~ spl8_2 ),
    inference(superposition,[],[f155,f155])).

fof(f155,plain,
    ( ! [X0] : k1_funct_1(sK3(sK0),sK1(sK3(sK0))) = X0
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl8_2
  <=> ! [X0] : k1_funct_1(sK3(sK0),sK1(sK3(sK0))) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f156,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f143,f154,f150])).

fof(f143,plain,(
    ! [X0] :
      ( k1_funct_1(sK3(sK0),sK1(sK3(sK0))) = X0
      | k1_xboole_0 = sK3(sK0) ) ),
    inference(superposition,[],[f105,f142])).

fof(f142,plain,(
    ! [X0] : sK3(sK0) = sK7(sK0,X0) ),
    inference(equality_resolution,[],[f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK7(X0,X1) = sK3(sK0) ) ),
    inference(equality_resolution,[],[f138])).

fof(f138,plain,(
    ! [X4,X2,X3] :
      ( sK0 != X4
      | sK0 != X2
      | sK7(X2,X3) = sK3(X4) ) ),
    inference(subsumption_resolution,[],[f137,f37])).

fof(f37,plain,(
    ! [X0,X1] : v1_relat_1(sK7(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f137,plain,(
    ! [X4,X2,X3] :
      ( sK0 != X2
      | sK0 != X4
      | ~ v1_relat_1(sK7(X2,X3))
      | sK7(X2,X3) = sK3(X4) ) ),
    inference(subsumption_resolution,[],[f133,f38])).

fof(f38,plain,(
    ! [X0,X1] : v1_funct_1(sK7(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f133,plain,(
    ! [X4,X2,X3] :
      ( sK0 != X2
      | ~ v1_funct_1(sK7(X2,X3))
      | sK0 != X4
      | ~ v1_relat_1(sK7(X2,X3))
      | sK7(X2,X3) = sK3(X4) ) ),
    inference(superposition,[],[f129,f39])).

fof(f39,plain,(
    ! [X0,X1] : k1_relat_1(sK7(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f129,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != sK0
      | ~ v1_funct_1(X1)
      | sK0 != X0
      | ~ v1_relat_1(X1)
      | sK3(X0) = X1 ) ),
    inference(subsumption_resolution,[],[f128,f28])).

fof(f28,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f128,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | ~ v1_funct_1(X1)
      | ~ v1_funct_1(sK3(X0))
      | k1_relat_1(X1) != sK0
      | ~ v1_relat_1(X1)
      | sK3(X0) = X1 ) ),
    inference(subsumption_resolution,[],[f125,f27])).

fof(f125,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(sK3(X0))
      | ~ v1_funct_1(sK3(X0))
      | k1_relat_1(X1) != sK0
      | ~ v1_relat_1(X1)
      | sK3(X0) = X1 ) ),
    inference(superposition,[],[f20,f29])).

fof(f20,plain,(
    ! [X2,X1] :
      ( k1_relat_1(X2) != sK0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X1) != sK0
      | ~ v1_relat_1(X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k1_funct_1(sK7(X0,X1),sK1(sK3(X0))) = X1
      | k1_xboole_0 = sK3(X0) ) ),
    inference(resolution,[],[f104,f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | k1_funct_1(sK7(X0,X1),X3) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f104,plain,(
    ! [X0] :
      ( r2_hidden(sK1(sK3(X0)),X0)
      | k1_xboole_0 = sK3(X0) ) ),
    inference(forward_demodulation,[],[f100,f29])).

fof(f100,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK3(X0)
      | r2_hidden(sK1(sK3(X0)),k1_relat_1(sK3(X0))) ) ),
    inference(resolution,[],[f90,f42])).

fof(f42,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f90,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK1(sK3(X0)),sK2(sK3(X0))),sK3(X0))
      | k1_xboole_0 = sK3(X0) ) ),
    inference(resolution,[],[f25,f27])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:27:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (23427)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (23418)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (23420)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.52  % (23419)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (23427)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f226,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f156,f208,f225])).
% 0.22/0.52  fof(f225,plain,(
% 0.22/0.52    ~spl8_1),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f224])).
% 0.22/0.52  fof(f224,plain,(
% 0.22/0.52    $false | ~spl8_1),
% 0.22/0.52    inference(subsumption_resolution,[],[f223,f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    k1_xboole_0 != sK0),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.52    inference(flattening,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,negated_conjecture,(
% 0.22/0.52    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.22/0.52    inference(negated_conjecture,[],[f9])).
% 0.22/0.52  fof(f9,conjecture,(
% 0.22/0.52    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).
% 0.22/0.52  fof(f223,plain,(
% 0.22/0.52    k1_xboole_0 = sK0 | ~spl8_1),
% 0.22/0.52    inference(forward_demodulation,[],[f217,f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.52    inference(superposition,[],[f29,f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    k1_xboole_0 = sK3(k1_xboole_0)),
% 0.22/0.52    inference(superposition,[],[f52,f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ( ! [X0] : (sK3(X0) = k7_relat_1(sK3(X0),X0)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f44,f29])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X0] : (sK3(X0) = k7_relat_1(sK3(X0),k1_relat_1(sK3(X0)))) )),
% 0.22/0.52    inference(resolution,[],[f24,f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    k1_xboole_0 = k7_relat_1(sK3(k1_xboole_0),k1_xboole_0)),
% 0.22/0.52    inference(resolution,[],[f50,f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.52    inference(equality_resolution,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ( ! [X0] : (r1_xboole_0(X0,X0) | k1_xboole_0 != X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k7_relat_1(sK3(X0),X1)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f48,f29])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(sK3(X0)),X1) | k1_xboole_0 = k7_relat_1(sK3(X0),X1)) )),
% 0.22/0.52    inference(resolution,[],[f30,f27])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f217,plain,(
% 0.22/0.52    sK0 = k1_relat_1(k1_xboole_0) | ~spl8_1),
% 0.22/0.52    inference(superposition,[],[f29,f152])).
% 0.22/0.52  fof(f152,plain,(
% 0.22/0.52    k1_xboole_0 = sK3(sK0) | ~spl8_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f150])).
% 0.22/0.52  fof(f150,plain,(
% 0.22/0.52    spl8_1 <=> k1_xboole_0 = sK3(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.52  fof(f208,plain,(
% 0.22/0.52    ~spl8_2),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f204])).
% 0.22/0.52  fof(f204,plain,(
% 0.22/0.52    $false | ~spl8_2),
% 0.22/0.52    inference(subsumption_resolution,[],[f21,f157])).
% 0.22/0.52  fof(f157,plain,(
% 0.22/0.52    ( ! [X0,X1] : (X0 = X1) ) | ~spl8_2),
% 0.22/0.52    inference(superposition,[],[f155,f155])).
% 0.22/0.52  fof(f155,plain,(
% 0.22/0.52    ( ! [X0] : (k1_funct_1(sK3(sK0),sK1(sK3(sK0))) = X0) ) | ~spl8_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f154])).
% 0.22/0.52  fof(f154,plain,(
% 0.22/0.52    spl8_2 <=> ! [X0] : k1_funct_1(sK3(sK0),sK1(sK3(sK0))) = X0),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.52  fof(f156,plain,(
% 0.22/0.52    spl8_1 | spl8_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f143,f154,f150])).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    ( ! [X0] : (k1_funct_1(sK3(sK0),sK1(sK3(sK0))) = X0 | k1_xboole_0 = sK3(sK0)) )),
% 0.22/0.52    inference(superposition,[],[f105,f142])).
% 0.22/0.52  fof(f142,plain,(
% 0.22/0.52    ( ! [X0] : (sK3(sK0) = sK7(sK0,X0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f141])).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    ( ! [X0,X1] : (sK0 != X0 | sK7(X0,X1) = sK3(sK0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f138])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    ( ! [X4,X2,X3] : (sK0 != X4 | sK0 != X2 | sK7(X2,X3) = sK3(X4)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f137,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(sK7(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 0.22/0.52  fof(f137,plain,(
% 0.22/0.52    ( ! [X4,X2,X3] : (sK0 != X2 | sK0 != X4 | ~v1_relat_1(sK7(X2,X3)) | sK7(X2,X3) = sK3(X4)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f133,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_funct_1(sK7(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f133,plain,(
% 0.22/0.52    ( ! [X4,X2,X3] : (sK0 != X2 | ~v1_funct_1(sK7(X2,X3)) | sK0 != X4 | ~v1_relat_1(sK7(X2,X3)) | sK7(X2,X3) = sK3(X4)) )),
% 0.22/0.52    inference(superposition,[],[f129,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_relat_1(sK7(X0,X1)) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_relat_1(X1) != sK0 | ~v1_funct_1(X1) | sK0 != X0 | ~v1_relat_1(X1) | sK3(X0) = X1) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f128,f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f128,plain,(
% 0.22/0.52    ( ! [X0,X1] : (sK0 != X0 | ~v1_funct_1(X1) | ~v1_funct_1(sK3(X0)) | k1_relat_1(X1) != sK0 | ~v1_relat_1(X1) | sK3(X0) = X1) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f125,f27])).
% 0.22/0.52  fof(f125,plain,(
% 0.22/0.52    ( ! [X0,X1] : (sK0 != X0 | ~v1_funct_1(X1) | ~v1_relat_1(sK3(X0)) | ~v1_funct_1(sK3(X0)) | k1_relat_1(X1) != sK0 | ~v1_relat_1(X1) | sK3(X0) = X1) )),
% 0.22/0.52    inference(superposition,[],[f20,f29])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ( ! [X2,X1] : (k1_relat_1(X2) != sK0 | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X1) != sK0 | ~v1_relat_1(X1) | X1 = X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_funct_1(sK7(X0,X1),sK1(sK3(X0))) = X1 | k1_xboole_0 = sK3(X0)) )),
% 0.22/0.52    inference(resolution,[],[f104,f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | k1_funct_1(sK7(X0,X1),X3) = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK1(sK3(X0)),X0) | k1_xboole_0 = sK3(X0)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f100,f29])).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = sK3(X0) | r2_hidden(sK1(sK3(X0)),k1_relat_1(sK3(X0)))) )),
% 0.22/0.52    inference(resolution,[],[f90,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 0.22/0.52    inference(equality_resolution,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(k4_tarski(sK1(sK3(X0)),sK2(sK3(X0))),sK3(X0)) | k1_xboole_0 = sK3(X0)) )),
% 0.22/0.52    inference(resolution,[],[f25,f27])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) | k1_xboole_0 = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (23427)------------------------------
% 0.22/0.52  % (23427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (23427)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (23427)Memory used [KB]: 10746
% 0.22/0.52  % (23427)Time elapsed: 0.105 s
% 0.22/0.52  % (23427)------------------------------
% 0.22/0.52  % (23427)------------------------------
% 0.22/0.52  % (23404)Success in time 0.157 s
%------------------------------------------------------------------------------
