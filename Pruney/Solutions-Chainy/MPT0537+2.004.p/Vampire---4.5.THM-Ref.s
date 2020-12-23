%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 (  67 expanded)
%              Number of leaves         :   15 (  30 expanded)
%              Depth                    :    5
%              Number of atoms          :  112 ( 152 expanded)
%              Number of equality atoms :   23 (  32 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f93,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f36,f40,f44,f48,f52,f61,f67,f89,f92])).

fof(f92,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f31,f60,f35,f66,f66,f88])).

fof(f88,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK2(X0,X1,X2),X0)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1)
        | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)
        | k8_relat_1(X0,X1) = X2 )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | r2_hidden(sK2(X0,X1,X2),X0)
        | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)
        | k8_relat_1(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f66,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl3_9
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f35,plain,
    ( k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_2
  <=> k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f60,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl3_8
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f31,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl3_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f89,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f16,f87])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)
      | k8_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).

% (24742)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f67,plain,
    ( spl3_9
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f62,f50,f46,f65])).

fof(f46,plain,
    ( spl3_5
  <=> ! [X1,X0] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f50,plain,
    ( spl3_6
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f62,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(superposition,[],[f47,f51])).

fof(f51,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f50])).

fof(f47,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f61,plain,
    ( spl3_8
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f57,f42,f38,f59])).

fof(f38,plain,
    ( spl3_3
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f42,plain,
    ( spl3_4
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f57,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(superposition,[],[f39,f43])).

fof(f43,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f39,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f52,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f27,f50])).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f48,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f14,f46])).

fof(f14,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f44,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f12,f42])).

fof(f12,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f40,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f13,f38])).

fof(f13,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f36,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f11,f34])).

fof(f11,plain,(
    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( k1_xboole_0 != k8_relat_1(k1_xboole_0,X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

fof(f32,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f10,f30])).

fof(f10,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (24736)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.46  % (24736)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f93,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f32,f36,f40,f44,f48,f52,f61,f67,f89,f92])).
% 0.20/0.46  fof(f92,plain,(
% 0.20/0.46    ~spl3_1 | spl3_2 | ~spl3_8 | ~spl3_9 | ~spl3_14),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f90])).
% 0.20/0.46  fof(f90,plain,(
% 0.20/0.46    $false | (~spl3_1 | spl3_2 | ~spl3_8 | ~spl3_9 | ~spl3_14)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f31,f60,f35,f66,f66,f88])).
% 0.20/0.46  fof(f88,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) | k8_relat_1(X0,X1) = X2) ) | ~spl3_14),
% 0.20/0.46    inference(avatar_component_clause,[],[f87])).
% 0.20/0.46  fof(f87,plain,(
% 0.20/0.46    spl3_14 <=> ! [X1,X0,X2] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) | k8_relat_1(X0,X1) = X2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.46  fof(f66,plain,(
% 0.20/0.46    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl3_9),
% 0.20/0.46    inference(avatar_component_clause,[],[f65])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    spl3_9 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) | spl3_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    spl3_2 <=> k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    v1_relat_1(k1_xboole_0) | ~spl3_8),
% 0.20/0.46    inference(avatar_component_clause,[],[f59])).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    spl3_8 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    v1_relat_1(sK0) | ~spl3_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    spl3_1 <=> v1_relat_1(sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.46  fof(f89,plain,(
% 0.20/0.46    spl3_14),
% 0.20/0.46    inference(avatar_split_clause,[],[f16,f87])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) | k8_relat_1(X0,X1) = X2) )),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0))))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).
% 0.20/0.46  % (24742)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    spl3_9 | ~spl3_5 | ~spl3_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f62,f50,f46,f65])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    spl3_5 <=> ! [X1,X0] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    spl3_6 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl3_5 | ~spl3_6)),
% 0.20/0.46    inference(superposition,[],[f47,f51])).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl3_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f50])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) ) | ~spl3_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f46])).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    spl3_8 | ~spl3_3 | ~spl3_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f57,f42,f38,f59])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    spl3_3 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    spl3_4 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    v1_relat_1(k1_xboole_0) | (~spl3_3 | ~spl3_4)),
% 0.20/0.46    inference(superposition,[],[f39,f43])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl3_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f42])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl3_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f38])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    spl3_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f27,f50])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.46    inference(equality_resolution,[],[f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    spl3_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f14,f46])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    spl3_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f12,f42])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    spl3_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f13,f38])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    ~spl3_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f11,f34])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ? [X0] : (k1_xboole_0 != k8_relat_1(k1_xboole_0,X0) & v1_relat_1(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,negated_conjecture,(
% 0.20/0.46    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 0.20/0.46    inference(negated_conjecture,[],[f6])).
% 0.20/0.46  fof(f6,conjecture,(
% 0.20/0.46    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    spl3_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f10,f30])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    v1_relat_1(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f8])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (24736)------------------------------
% 0.20/0.46  % (24736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (24736)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (24736)Memory used [KB]: 10618
% 0.20/0.46  % (24736)Time elapsed: 0.043 s
% 0.20/0.46  % (24736)------------------------------
% 0.20/0.46  % (24736)------------------------------
% 0.20/0.46  % (24734)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (24726)Success in time 0.107 s
%------------------------------------------------------------------------------
