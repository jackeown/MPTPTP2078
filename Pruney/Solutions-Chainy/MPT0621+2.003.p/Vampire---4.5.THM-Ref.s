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
% DateTime   : Thu Dec  3 12:51:55 EST 2020

% Result     : Theorem 1.12s
% Output     : Refutation 1.12s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 151 expanded)
%              Number of leaves         :   14 (  46 expanded)
%              Depth                    :   18
%              Number of atoms          :  243 ( 636 expanded)
%              Number of equality atoms :   95 ( 221 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f183,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f164,f169,f182])).

fof(f182,plain,(
    ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f179,f45])).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f179,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f44,f162])).

fof(f162,plain,
    ( k1_xboole_0 = np__1
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl8_2
  <=> k1_xboole_0 = np__1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f44,plain,(
    ~ v1_xboole_0(np__1) ),
    inference(cnf_transformation,[],[f10])).

% (15131)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f10,axiom,(
    ~ v1_xboole_0(np__1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',spc1_boole)).

fof(f169,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | spl8_1 ),
    inference(subsumption_resolution,[],[f166,f43])).

fof(f43,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f23])).

fof(f23,plain,
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

fof(f166,plain,
    ( k1_xboole_0 = sK0
    | spl8_1 ),
    inference(resolution,[],[f165,f146])).

fof(f146,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f143,f57])).

fof(f57,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f143,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0,k1_xboole_0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f140,f45])).

fof(f140,plain,(
    ! [X2,X3] :
      ( ~ v1_xboole_0(X3)
      | r2_hidden(sK7(X2,X3),X2)
      | X2 = X3 ) ),
    inference(resolution,[],[f67,f57])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK7(X0,X1),X1)
          | ~ r2_hidden(sK7(X0,X1),X0) )
        & ( r2_hidden(sK7(X0,X1),X1)
          | r2_hidden(sK7(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK7(X0,X1),X1)
          | ~ r2_hidden(sK7(X0,X1),X0) )
        & ( r2_hidden(sK7(X0,X1),X1)
          | r2_hidden(sK7(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f165,plain,
    ( v1_xboole_0(sK0)
    | spl8_1 ),
    inference(resolution,[],[f158,f58])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f158,plain,
    ( ~ r2_hidden(sK4(sK0),sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl8_1
  <=> r2_hidden(sK4(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f164,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f154,f160,f156])).

fof(f154,plain,
    ( k1_xboole_0 = np__1
    | ~ r2_hidden(sK4(sK0),sK0) ),
    inference(superposition,[],[f62,f152])).

fof(f152,plain,(
    np__1 = k1_funct_1(sK5(sK0),sK4(sK0)) ),
    inference(subsumption_resolution,[],[f150,f43])).

fof(f150,plain,
    ( np__1 = k1_funct_1(sK5(sK0),sK4(sK0))
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f149,f89])).

fof(f89,plain,(
    sK5(sK0) = sK6(sK0) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( sK0 != X0
      | sK5(X0) = sK6(sK0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK0 != X1
      | sK6(X0) = sK5(X1) ) ),
    inference(superposition,[],[f83,f65])).

fof(f65,plain,(
    ! [X0] : k1_relat_1(sK6(X0)) = X0 ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X2] :
          ( np__1 = k1_funct_1(sK6(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK6(X0)) = X0
      & v1_funct_1(sK6(X0))
      & v1_relat_1(sK6(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_funct_1(X1,X2) = np__1
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( np__1 = k1_funct_1(sK6(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK6(X0)) = X0
        & v1_funct_1(sK6(X0))
        & v1_relat_1(sK6(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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

fof(f83,plain,(
    ! [X2,X3] :
      ( sK0 != k1_relat_1(sK6(X2))
      | sK0 != X3
      | sK6(X2) = sK5(X3) ) ),
    inference(subsumption_resolution,[],[f81,f64])).

fof(f64,plain,(
    ! [X0] : v1_funct_1(sK6(X0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f81,plain,(
    ! [X2,X3] :
      ( sK0 != k1_relat_1(sK6(X2))
      | ~ v1_funct_1(sK6(X2))
      | sK0 != X3
      | sK6(X2) = sK5(X3) ) ),
    inference(resolution,[],[f77,f63])).

fof(f63,plain,(
    ! [X0] : v1_relat_1(sK6(X0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) != sK0
      | ~ v1_funct_1(X0)
      | sK0 != X1
      | sK5(X1) = X0 ) ),
    inference(forward_demodulation,[],[f76,f61])).

fof(f61,plain,(
    ! [X0] : k1_relat_1(sK5(X0)) = X0 ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK5(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK5(X0)) = X0
      & v1_funct_1(sK5(X0))
      & v1_relat_1(sK5(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK5(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK5(X0)) = X0
        & v1_funct_1(sK5(X0))
        & v1_relat_1(sK5(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != sK0
      | sK0 != k1_relat_1(sK5(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK5(X1) = X0 ) ),
    inference(subsumption_resolution,[],[f74,f60])).

fof(f60,plain,(
    ! [X0] : v1_funct_1(sK5(X0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != sK0
      | sK0 != k1_relat_1(sK5(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK5(X1))
      | sK5(X1) = X0 ) ),
    inference(resolution,[],[f42,f59])).

fof(f59,plain,(
    ! [X0] : v1_relat_1(sK5(X0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f42,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(X2) != sK0
      | k1_relat_1(X1) != sK0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f149,plain,(
    ! [X0] :
      ( np__1 = k1_funct_1(sK6(X0),sK4(X0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f146,f107])).

fof(f107,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | np__1 = k1_funct_1(sK6(X0),sK4(X0)) ) ),
    inference(resolution,[],[f66,f58])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | np__1 = k1_funct_1(sK6(X0),X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = k1_funct_1(sK5(X0),X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:16:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (15127)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.12/0.51  % (15127)Refutation found. Thanks to Tanya!
% 1.12/0.51  % SZS status Theorem for theBenchmark
% 1.12/0.51  % (15144)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.12/0.51  % (15136)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.12/0.52  % (15126)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.12/0.52  % (15129)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.12/0.52  % (15144)Refutation not found, incomplete strategy% (15144)------------------------------
% 1.12/0.52  % (15144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.12/0.52  % SZS output start Proof for theBenchmark
% 1.12/0.52  fof(f183,plain,(
% 1.12/0.52    $false),
% 1.12/0.52    inference(avatar_sat_refutation,[],[f164,f169,f182])).
% 1.12/0.52  fof(f182,plain,(
% 1.12/0.52    ~spl8_2),
% 1.12/0.52    inference(avatar_contradiction_clause,[],[f181])).
% 1.12/0.52  fof(f181,plain,(
% 1.12/0.52    $false | ~spl8_2),
% 1.12/0.52    inference(subsumption_resolution,[],[f179,f45])).
% 1.12/0.52  fof(f45,plain,(
% 1.12/0.52    v1_xboole_0(k1_xboole_0)),
% 1.12/0.52    inference(cnf_transformation,[],[f2])).
% 1.12/0.52  fof(f2,axiom,(
% 1.12/0.52    v1_xboole_0(k1_xboole_0)),
% 1.12/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.12/0.52  fof(f179,plain,(
% 1.12/0.52    ~v1_xboole_0(k1_xboole_0) | ~spl8_2),
% 1.12/0.52    inference(backward_demodulation,[],[f44,f162])).
% 1.12/0.52  fof(f162,plain,(
% 1.12/0.52    k1_xboole_0 = np__1 | ~spl8_2),
% 1.12/0.52    inference(avatar_component_clause,[],[f160])).
% 1.12/0.52  fof(f160,plain,(
% 1.12/0.52    spl8_2 <=> k1_xboole_0 = np__1),
% 1.12/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.12/0.52  fof(f44,plain,(
% 1.12/0.52    ~v1_xboole_0(np__1)),
% 1.12/0.52    inference(cnf_transformation,[],[f10])).
% 1.12/0.52  % (15131)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.12/0.52  fof(f10,axiom,(
% 1.12/0.52    ~v1_xboole_0(np__1)),
% 1.12/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',spc1_boole)).
% 1.12/0.52  fof(f169,plain,(
% 1.12/0.52    spl8_1),
% 1.12/0.52    inference(avatar_contradiction_clause,[],[f168])).
% 1.12/0.52  fof(f168,plain,(
% 1.12/0.52    $false | spl8_1),
% 1.12/0.52    inference(subsumption_resolution,[],[f166,f43])).
% 1.12/0.52  fof(f43,plain,(
% 1.12/0.52    k1_xboole_0 != sK0),
% 1.12/0.52    inference(cnf_transformation,[],[f24])).
% 1.12/0.52  fof(f24,plain,(
% 1.12/0.52    k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.12/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f23])).
% 1.12/0.52  fof(f23,plain,(
% 1.12/0.52    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.12/0.52    introduced(choice_axiom,[])).
% 1.12/0.52  fof(f14,plain,(
% 1.12/0.52    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.12/0.52    inference(flattening,[],[f13])).
% 1.12/0.52  fof(f13,plain,(
% 1.12/0.52    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 1.12/0.52    inference(ennf_transformation,[],[f12])).
% 1.12/0.52  fof(f12,negated_conjecture,(
% 1.12/0.52    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 1.12/0.52    inference(negated_conjecture,[],[f11])).
% 1.12/0.52  fof(f11,conjecture,(
% 1.12/0.52    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 1.12/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).
% 1.12/0.52  fof(f166,plain,(
% 1.12/0.52    k1_xboole_0 = sK0 | spl8_1),
% 1.12/0.52    inference(resolution,[],[f165,f146])).
% 1.12/0.52  fof(f146,plain,(
% 1.12/0.52    ( ! [X1] : (~v1_xboole_0(X1) | k1_xboole_0 = X1) )),
% 1.12/0.52    inference(resolution,[],[f143,f57])).
% 1.12/0.52  fof(f57,plain,(
% 1.12/0.52    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.12/0.52    inference(cnf_transformation,[],[f34])).
% 1.12/0.52  fof(f34,plain,(
% 1.12/0.52    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.12/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).
% 1.12/0.52  fof(f33,plain,(
% 1.12/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.12/0.52    introduced(choice_axiom,[])).
% 1.12/0.52  fof(f32,plain,(
% 1.12/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.12/0.52    inference(rectify,[],[f31])).
% 1.12/0.52  fof(f31,plain,(
% 1.12/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.12/0.52    inference(nnf_transformation,[],[f1])).
% 1.12/0.52  fof(f1,axiom,(
% 1.12/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.12/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.12/0.52  fof(f143,plain,(
% 1.12/0.52    ( ! [X0] : (r2_hidden(sK7(X0,k1_xboole_0),X0) | k1_xboole_0 = X0) )),
% 1.12/0.52    inference(resolution,[],[f140,f45])).
% 1.12/0.52  fof(f140,plain,(
% 1.12/0.52    ( ! [X2,X3] : (~v1_xboole_0(X3) | r2_hidden(sK7(X2,X3),X2) | X2 = X3) )),
% 1.12/0.52    inference(resolution,[],[f67,f57])).
% 1.12/0.52  fof(f67,plain,(
% 1.12/0.52    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X1) | X0 = X1 | r2_hidden(sK7(X0,X1),X0)) )),
% 1.12/0.52    inference(cnf_transformation,[],[f41])).
% 1.12/0.52  fof(f41,plain,(
% 1.12/0.52    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK7(X0,X1),X1) | ~r2_hidden(sK7(X0,X1),X0)) & (r2_hidden(sK7(X0,X1),X1) | r2_hidden(sK7(X0,X1),X0))))),
% 1.12/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f39,f40])).
% 1.12/0.52  fof(f40,plain,(
% 1.12/0.52    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK7(X0,X1),X1) | ~r2_hidden(sK7(X0,X1),X0)) & (r2_hidden(sK7(X0,X1),X1) | r2_hidden(sK7(X0,X1),X0))))),
% 1.12/0.52    introduced(choice_axiom,[])).
% 1.12/0.52  fof(f39,plain,(
% 1.12/0.52    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 1.12/0.52    inference(nnf_transformation,[],[f22])).
% 1.12/0.52  fof(f22,plain,(
% 1.12/0.52    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.12/0.52    inference(ennf_transformation,[],[f3])).
% 1.12/0.52  fof(f3,axiom,(
% 1.12/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.12/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 1.12/0.52  fof(f165,plain,(
% 1.12/0.52    v1_xboole_0(sK0) | spl8_1),
% 1.12/0.52    inference(resolution,[],[f158,f58])).
% 1.12/0.52  fof(f58,plain,(
% 1.12/0.52    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 1.12/0.52    inference(cnf_transformation,[],[f34])).
% 1.12/0.52  fof(f158,plain,(
% 1.12/0.52    ~r2_hidden(sK4(sK0),sK0) | spl8_1),
% 1.12/0.52    inference(avatar_component_clause,[],[f156])).
% 1.12/0.52  fof(f156,plain,(
% 1.12/0.52    spl8_1 <=> r2_hidden(sK4(sK0),sK0)),
% 1.12/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.12/0.52  fof(f164,plain,(
% 1.12/0.52    ~spl8_1 | spl8_2),
% 1.12/0.52    inference(avatar_split_clause,[],[f154,f160,f156])).
% 1.12/0.52  fof(f154,plain,(
% 1.12/0.52    k1_xboole_0 = np__1 | ~r2_hidden(sK4(sK0),sK0)),
% 1.12/0.52    inference(superposition,[],[f62,f152])).
% 1.12/0.52  fof(f152,plain,(
% 1.12/0.52    np__1 = k1_funct_1(sK5(sK0),sK4(sK0))),
% 1.12/0.52    inference(subsumption_resolution,[],[f150,f43])).
% 1.12/0.52  fof(f150,plain,(
% 1.12/0.52    np__1 = k1_funct_1(sK5(sK0),sK4(sK0)) | k1_xboole_0 = sK0),
% 1.12/0.52    inference(superposition,[],[f149,f89])).
% 1.12/0.52  fof(f89,plain,(
% 1.12/0.52    sK5(sK0) = sK6(sK0)),
% 1.12/0.52    inference(equality_resolution,[],[f88])).
% 1.12/0.52  fof(f88,plain,(
% 1.12/0.52    ( ! [X0] : (sK0 != X0 | sK5(X0) = sK6(sK0)) )),
% 1.12/0.52    inference(equality_resolution,[],[f87])).
% 1.12/0.52  fof(f87,plain,(
% 1.12/0.52    ( ! [X0,X1] : (sK0 != X0 | sK0 != X1 | sK6(X0) = sK5(X1)) )),
% 1.12/0.52    inference(superposition,[],[f83,f65])).
% 1.12/0.52  fof(f65,plain,(
% 1.12/0.52    ( ! [X0] : (k1_relat_1(sK6(X0)) = X0) )),
% 1.12/0.52    inference(cnf_transformation,[],[f38])).
% 1.12/0.52  fof(f38,plain,(
% 1.12/0.52    ! [X0] : (! [X2] : (np__1 = k1_funct_1(sK6(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK6(X0)) = X0 & v1_funct_1(sK6(X0)) & v1_relat_1(sK6(X0)))),
% 1.12/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f37])).
% 1.12/0.52  fof(f37,plain,(
% 1.12/0.52    ! [X0] : (? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (np__1 = k1_funct_1(sK6(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK6(X0)) = X0 & v1_funct_1(sK6(X0)) & v1_relat_1(sK6(X0))))),
% 1.12/0.52    introduced(choice_axiom,[])).
% 1.12/0.52  fof(f21,plain,(
% 1.12/0.52    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.12/0.52    inference(ennf_transformation,[],[f9])).
% 1.12/0.52  fof(f9,axiom,(
% 1.12/0.52    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = np__1) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.12/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).
% 1.12/0.52  fof(f83,plain,(
% 1.12/0.52    ( ! [X2,X3] : (sK0 != k1_relat_1(sK6(X2)) | sK0 != X3 | sK6(X2) = sK5(X3)) )),
% 1.12/0.52    inference(subsumption_resolution,[],[f81,f64])).
% 1.12/0.52  fof(f64,plain,(
% 1.12/0.52    ( ! [X0] : (v1_funct_1(sK6(X0))) )),
% 1.12/0.52    inference(cnf_transformation,[],[f38])).
% 1.12/0.52  fof(f81,plain,(
% 1.12/0.52    ( ! [X2,X3] : (sK0 != k1_relat_1(sK6(X2)) | ~v1_funct_1(sK6(X2)) | sK0 != X3 | sK6(X2) = sK5(X3)) )),
% 1.12/0.52    inference(resolution,[],[f77,f63])).
% 1.12/0.52  fof(f63,plain,(
% 1.12/0.52    ( ! [X0] : (v1_relat_1(sK6(X0))) )),
% 1.12/0.52    inference(cnf_transformation,[],[f38])).
% 1.12/0.52  fof(f77,plain,(
% 1.12/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_relat_1(X0) != sK0 | ~v1_funct_1(X0) | sK0 != X1 | sK5(X1) = X0) )),
% 1.12/0.52    inference(forward_demodulation,[],[f76,f61])).
% 1.12/0.52  fof(f61,plain,(
% 1.12/0.52    ( ! [X0] : (k1_relat_1(sK5(X0)) = X0) )),
% 1.12/0.52    inference(cnf_transformation,[],[f36])).
% 1.12/0.52  fof(f36,plain,(
% 1.12/0.52    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK5(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK5(X0)) = X0 & v1_funct_1(sK5(X0)) & v1_relat_1(sK5(X0)))),
% 1.12/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f35])).
% 1.12/0.52  fof(f35,plain,(
% 1.12/0.52    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK5(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK5(X0)) = X0 & v1_funct_1(sK5(X0)) & v1_relat_1(sK5(X0))))),
% 1.12/0.52    introduced(choice_axiom,[])).
% 1.12/0.52  fof(f20,plain,(
% 1.12/0.52    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.12/0.52    inference(ennf_transformation,[],[f8])).
% 1.12/0.52  fof(f8,axiom,(
% 1.12/0.52    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.12/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 1.12/0.52  fof(f76,plain,(
% 1.12/0.52    ( ! [X0,X1] : (k1_relat_1(X0) != sK0 | sK0 != k1_relat_1(sK5(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK5(X1) = X0) )),
% 1.12/0.52    inference(subsumption_resolution,[],[f74,f60])).
% 1.12/0.52  fof(f60,plain,(
% 1.12/0.52    ( ! [X0] : (v1_funct_1(sK5(X0))) )),
% 1.12/0.52    inference(cnf_transformation,[],[f36])).
% 1.12/0.52  fof(f74,plain,(
% 1.12/0.52    ( ! [X0,X1] : (k1_relat_1(X0) != sK0 | sK0 != k1_relat_1(sK5(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK5(X1)) | sK5(X1) = X0) )),
% 1.12/0.52    inference(resolution,[],[f42,f59])).
% 1.12/0.52  fof(f59,plain,(
% 1.12/0.52    ( ! [X0] : (v1_relat_1(sK5(X0))) )),
% 1.12/0.52    inference(cnf_transformation,[],[f36])).
% 1.12/0.52  fof(f42,plain,(
% 1.12/0.52    ( ! [X2,X1] : (~v1_relat_1(X1) | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | X1 = X2) )),
% 1.12/0.52    inference(cnf_transformation,[],[f24])).
% 1.12/0.52  fof(f149,plain,(
% 1.12/0.52    ( ! [X0] : (np__1 = k1_funct_1(sK6(X0),sK4(X0)) | k1_xboole_0 = X0) )),
% 1.12/0.52    inference(resolution,[],[f146,f107])).
% 1.12/0.52  fof(f107,plain,(
% 1.12/0.52    ( ! [X0] : (v1_xboole_0(X0) | np__1 = k1_funct_1(sK6(X0),sK4(X0))) )),
% 1.12/0.52    inference(resolution,[],[f66,f58])).
% 1.12/0.52  fof(f66,plain,(
% 1.12/0.52    ( ! [X2,X0] : (~r2_hidden(X2,X0) | np__1 = k1_funct_1(sK6(X0),X2)) )),
% 1.12/0.52    inference(cnf_transformation,[],[f38])).
% 1.12/0.52  fof(f62,plain,(
% 1.12/0.52    ( ! [X2,X0] : (k1_xboole_0 = k1_funct_1(sK5(X0),X2) | ~r2_hidden(X2,X0)) )),
% 1.12/0.52    inference(cnf_transformation,[],[f36])).
% 1.12/0.52  % SZS output end Proof for theBenchmark
% 1.12/0.52  % (15127)------------------------------
% 1.12/0.52  % (15127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.12/0.52  % (15127)Termination reason: Refutation
% 1.12/0.52  
% 1.12/0.52  % (15127)Memory used [KB]: 10746
% 1.12/0.52  % (15127)Time elapsed: 0.090 s
% 1.12/0.52  % (15127)------------------------------
% 1.12/0.52  % (15127)------------------------------
% 1.12/0.52  % (15144)Termination reason: Refutation not found, incomplete strategy
% 1.12/0.52  
% 1.12/0.52  % (15144)Memory used [KB]: 10746
% 1.12/0.52  % (15144)Time elapsed: 0.109 s
% 1.12/0.52  % (15144)------------------------------
% 1.12/0.52  % (15144)------------------------------
% 1.12/0.52  % (15123)Success in time 0.16 s
%------------------------------------------------------------------------------
