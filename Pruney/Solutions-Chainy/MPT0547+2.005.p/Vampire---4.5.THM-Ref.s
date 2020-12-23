%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:21 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   45 (  55 expanded)
%              Number of leaves         :   12 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :  125 ( 147 expanded)
%              Number of equality atoms :   30 (  37 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f44,f62,f65])).

fof(f65,plain,
    ( spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f63,f60,f38])).

fof(f38,plain,
    ( spl3_1
  <=> k1_xboole_0 = k9_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f60,plain,
    ( spl3_4
  <=> v1_xboole_0(k9_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f63,plain,
    ( k1_xboole_0 = k9_relat_1(sK0,k1_xboole_0)
    | ~ spl3_4 ),
    inference(resolution,[],[f61,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f61,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k1_xboole_0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f62,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f57,f42,f60])).

fof(f42,plain,
    ( spl3_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f57,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k1_xboole_0))
    | ~ spl3_2 ),
    inference(resolution,[],[f56,f26])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f56,plain,
    ( ! [X0] : ~ r2_hidden(X0,k9_relat_1(sK0,k1_xboole_0))
    | ~ spl3_2 ),
    inference(resolution,[],[f55,f45])).

fof(f45,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f27,f35])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f27,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f55,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1,sK0),X1)
        | ~ r2_hidden(X0,k9_relat_1(sK0,X1)) )
    | ~ spl3_2 ),
    inference(resolution,[],[f33,f43])).

fof(f43,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK2(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
            & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f44,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f23,f42])).

fof(f23,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k1_xboole_0 != k9_relat_1(sK0,k1_xboole_0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k9_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != k9_relat_1(sK0,k1_xboole_0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

% (7695)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% (7693)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f9,plain,(
    ? [X0] :
      ( k1_xboole_0 != k9_relat_1(X0,k1_xboole_0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

fof(f40,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f24,f38])).

fof(f24,plain,(
    k1_xboole_0 != k9_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:33:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.47  % (7699)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.47  % (7691)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.48  % (7697)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.48  % (7691)Refutation found. Thanks to Tanya!
% 0.19/0.48  % SZS status Theorem for theBenchmark
% 0.19/0.48  % SZS output start Proof for theBenchmark
% 0.19/0.48  fof(f66,plain,(
% 0.19/0.48    $false),
% 0.19/0.48    inference(avatar_sat_refutation,[],[f40,f44,f62,f65])).
% 0.19/0.48  fof(f65,plain,(
% 0.19/0.48    spl3_1 | ~spl3_4),
% 0.19/0.48    inference(avatar_split_clause,[],[f63,f60,f38])).
% 0.19/0.48  fof(f38,plain,(
% 0.19/0.48    spl3_1 <=> k1_xboole_0 = k9_relat_1(sK0,k1_xboole_0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.48  fof(f60,plain,(
% 0.19/0.48    spl3_4 <=> v1_xboole_0(k9_relat_1(sK0,k1_xboole_0))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.48  fof(f63,plain,(
% 0.19/0.48    k1_xboole_0 = k9_relat_1(sK0,k1_xboole_0) | ~spl3_4),
% 0.19/0.48    inference(resolution,[],[f61,f25])).
% 0.19/0.48  fof(f25,plain,(
% 0.19/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.19/0.48    inference(cnf_transformation,[],[f10])).
% 0.19/0.48  fof(f10,plain,(
% 0.19/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f2])).
% 0.19/0.48  fof(f2,axiom,(
% 0.19/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.19/0.48  fof(f61,plain,(
% 0.19/0.48    v1_xboole_0(k9_relat_1(sK0,k1_xboole_0)) | ~spl3_4),
% 0.19/0.48    inference(avatar_component_clause,[],[f60])).
% 0.19/0.48  fof(f62,plain,(
% 0.19/0.48    spl3_4 | ~spl3_2),
% 0.19/0.48    inference(avatar_split_clause,[],[f57,f42,f60])).
% 0.19/0.48  fof(f42,plain,(
% 0.19/0.48    spl3_2 <=> v1_relat_1(sK0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.48  fof(f57,plain,(
% 0.19/0.48    v1_xboole_0(k9_relat_1(sK0,k1_xboole_0)) | ~spl3_2),
% 0.19/0.48    inference(resolution,[],[f56,f26])).
% 0.19/0.48  fof(f26,plain,(
% 0.19/0.48    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_xboole_0(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f16])).
% 0.19/0.48  fof(f16,plain,(
% 0.19/0.48    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK1(X0),X0))),
% 0.19/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f15])).
% 0.19/0.48  fof(f15,plain,(
% 0.19/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f11,plain,(
% 0.19/0.48    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f8])).
% 0.19/0.48  fof(f8,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 0.19/0.48    inference(unused_predicate_definition_removal,[],[f1])).
% 0.19/0.48  fof(f1,axiom,(
% 0.19/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.19/0.48  fof(f56,plain,(
% 0.19/0.48    ( ! [X0] : (~r2_hidden(X0,k9_relat_1(sK0,k1_xboole_0))) ) | ~spl3_2),
% 0.19/0.48    inference(resolution,[],[f55,f45])).
% 0.19/0.48  fof(f45,plain,(
% 0.19/0.48    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.19/0.48    inference(superposition,[],[f27,f35])).
% 0.19/0.48  fof(f35,plain,(
% 0.19/0.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.19/0.48    inference(equality_resolution,[],[f30])).
% 0.19/0.48  fof(f30,plain,(
% 0.19/0.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.19/0.48    inference(cnf_transformation,[],[f18])).
% 0.19/0.48  fof(f18,plain,(
% 0.19/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.19/0.48    inference(flattening,[],[f17])).
% 0.19/0.48  fof(f17,plain,(
% 0.19/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.19/0.48    inference(nnf_transformation,[],[f3])).
% 0.19/0.48  fof(f3,axiom,(
% 0.19/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.48  fof(f27,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f4])).
% 0.19/0.48  fof(f4,axiom,(
% 0.19/0.48    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.19/0.48  fof(f55,plain,(
% 0.19/0.48    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,sK0),X1) | ~r2_hidden(X0,k9_relat_1(sK0,X1))) ) | ~spl3_2),
% 0.19/0.48    inference(resolution,[],[f33,f43])).
% 0.19/0.48  fof(f43,plain,(
% 0.19/0.48    v1_relat_1(sK0) | ~spl3_2),
% 0.19/0.48    inference(avatar_component_clause,[],[f42])).
% 0.19/0.48  fof(f33,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK2(X0,X1,X2),X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f22])).
% 0.19/0.48  fof(f22,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.19/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).
% 0.19/0.48  fof(f21,plain,(
% 0.19/0.48    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f20,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.19/0.48    inference(rectify,[],[f19])).
% 0.19/0.48  fof(f19,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.19/0.48    inference(nnf_transformation,[],[f12])).
% 0.19/0.48  fof(f12,plain,(
% 0.19/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.19/0.48    inference(ennf_transformation,[],[f5])).
% 0.19/0.48  fof(f5,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.19/0.48  fof(f44,plain,(
% 0.19/0.48    spl3_2),
% 0.19/0.48    inference(avatar_split_clause,[],[f23,f42])).
% 0.19/0.48  fof(f23,plain,(
% 0.19/0.48    v1_relat_1(sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f14])).
% 0.19/0.48  fof(f14,plain,(
% 0.19/0.48    k1_xboole_0 != k9_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0)),
% 0.19/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).
% 0.19/0.48  fof(f13,plain,(
% 0.19/0.48    ? [X0] : (k1_xboole_0 != k9_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => (k1_xboole_0 != k9_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  % (7695)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.19/0.48  % (7693)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.19/0.48  fof(f9,plain,(
% 0.19/0.48    ? [X0] : (k1_xboole_0 != k9_relat_1(X0,k1_xboole_0) & v1_relat_1(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f7])).
% 0.19/0.48  fof(f7,negated_conjecture,(
% 0.19/0.48    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 0.19/0.48    inference(negated_conjecture,[],[f6])).
% 0.19/0.48  fof(f6,conjecture,(
% 0.19/0.48    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).
% 0.19/0.48  fof(f40,plain,(
% 0.19/0.48    ~spl3_1),
% 0.19/0.48    inference(avatar_split_clause,[],[f24,f38])).
% 0.19/0.48  fof(f24,plain,(
% 0.19/0.48    k1_xboole_0 != k9_relat_1(sK0,k1_xboole_0)),
% 0.19/0.48    inference(cnf_transformation,[],[f14])).
% 0.19/0.48  % SZS output end Proof for theBenchmark
% 0.19/0.48  % (7691)------------------------------
% 0.19/0.48  % (7691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (7691)Termination reason: Refutation
% 0.19/0.48  
% 0.19/0.48  % (7691)Memory used [KB]: 10618
% 0.19/0.48  % (7691)Time elapsed: 0.010 s
% 0.19/0.48  % (7691)------------------------------
% 0.19/0.48  % (7691)------------------------------
% 0.19/0.48  % (7703)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.19/0.49  % (7684)Success in time 0.133 s
%------------------------------------------------------------------------------
