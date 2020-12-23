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
% DateTime   : Thu Dec  3 12:48:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 (  74 expanded)
%              Number of leaves         :   17 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :  131 ( 166 expanded)
%              Number of equality atoms :   40 (  51 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f94,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f33,f37,f41,f45,f49,f57,f63,f71,f86,f93])).

fof(f93,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f91,f28])).

fof(f28,plain,
    ( k1_xboole_0 != k3_relat_1(k1_xboole_0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl3_1
  <=> k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f91,plain,
    ( k1_xboole_0 = k3_relat_1(k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f90,f40])).

fof(f40,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_4
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f90,plain,
    ( k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f89,f32])).

fof(f32,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl3_2
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f89,plain,
    ( k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f87,f36])).

fof(f36,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_3
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f87,plain,
    ( k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(resolution,[],[f85,f62])).

fof(f62,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_9
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f85,plain,
    ( ! [X0] :
        ( r2_hidden(sK0(X0),X0)
        | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl3_14
  <=> ! [X0] :
        ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
        | r2_hidden(sK0(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f86,plain,
    ( spl3_14
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f76,f69,f55,f84])).

fof(f55,plain,
    ( spl3_8
  <=> ! [X0] :
        ( r2_hidden(sK0(X0),X0)
        | v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f69,plain,
    ( spl3_11
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f76,plain,
    ( ! [X0] :
        ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
        | r2_hidden(sK0(X0),X0) )
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(resolution,[],[f70,f56])).

fof(f56,plain,
    ( ! [X0] :
        ( v1_relat_1(X0)
        | r2_hidden(sK0(X0),X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f55])).

fof(f70,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f69])).

fof(f71,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f16,f69])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f63,plain,
    ( spl3_9
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f58,f47,f43,f61])).

fof(f43,plain,
    ( spl3_5
  <=> ! [X1,X0] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f47,plain,
    ( spl3_6
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f58,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(superposition,[],[f44,f48])).

fof(f48,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f47])).

fof(f44,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f43])).

fof(f57,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f18,f55])).

fof(f18,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f49,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f24,f47])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f45,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f20,f43])).

fof(f20,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f41,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f15,f39])).

fof(f15,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f37,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f14,f35])).

fof(f14,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f33,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f13,f31])).

fof(f13,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f29,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f12,f27])).

fof(f12,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f8])).

fof(f8,negated_conjecture,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:19:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (8990)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.42  % (8990)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f94,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f29,f33,f37,f41,f45,f49,f57,f63,f71,f86,f93])).
% 0.20/0.42  fof(f93,plain,(
% 0.20/0.42    spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_9 | ~spl3_14),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f92])).
% 0.20/0.42  fof(f92,plain,(
% 0.20/0.42    $false | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_9 | ~spl3_14)),
% 0.20/0.42    inference(subsumption_resolution,[],[f91,f28])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    k1_xboole_0 != k3_relat_1(k1_xboole_0) | spl3_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f27])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    spl3_1 <=> k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.42  fof(f91,plain,(
% 0.20/0.42    k1_xboole_0 = k3_relat_1(k1_xboole_0) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_9 | ~spl3_14)),
% 0.20/0.42    inference(forward_demodulation,[],[f90,f40])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f39])).
% 0.20/0.42  fof(f39,plain,(
% 0.20/0.42    spl3_4 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.42  fof(f90,plain,(
% 0.20/0.42    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl3_2 | ~spl3_3 | ~spl3_9 | ~spl3_14)),
% 0.20/0.42    inference(forward_demodulation,[],[f89,f32])).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f31])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    spl3_2 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.42  fof(f89,plain,(
% 0.20/0.42    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl3_3 | ~spl3_9 | ~spl3_14)),
% 0.20/0.42    inference(forward_demodulation,[],[f87,f36])).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl3_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f35])).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    spl3_3 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.42  fof(f87,plain,(
% 0.20/0.42    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) | (~spl3_9 | ~spl3_14)),
% 0.20/0.42    inference(resolution,[],[f85,f62])).
% 0.20/0.42  fof(f62,plain,(
% 0.20/0.42    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl3_9),
% 0.20/0.42    inference(avatar_component_clause,[],[f61])).
% 0.20/0.42  fof(f61,plain,(
% 0.20/0.42    spl3_9 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.42  fof(f85,plain,(
% 0.20/0.42    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) ) | ~spl3_14),
% 0.20/0.42    inference(avatar_component_clause,[],[f84])).
% 0.20/0.42  fof(f84,plain,(
% 0.20/0.42    spl3_14 <=> ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | r2_hidden(sK0(X0),X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.42  fof(f86,plain,(
% 0.20/0.42    spl3_14 | ~spl3_8 | ~spl3_11),
% 0.20/0.42    inference(avatar_split_clause,[],[f76,f69,f55,f84])).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    spl3_8 <=> ! [X0] : (r2_hidden(sK0(X0),X0) | v1_relat_1(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.42  fof(f69,plain,(
% 0.20/0.42    spl3_11 <=> ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.42  fof(f76,plain,(
% 0.20/0.42    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | r2_hidden(sK0(X0),X0)) ) | (~spl3_8 | ~spl3_11)),
% 0.20/0.42    inference(resolution,[],[f70,f56])).
% 0.20/0.42  fof(f56,plain,(
% 0.20/0.42    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK0(X0),X0)) ) | ~spl3_8),
% 0.20/0.42    inference(avatar_component_clause,[],[f55])).
% 0.20/0.42  fof(f70,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) ) | ~spl3_11),
% 0.20/0.42    inference(avatar_component_clause,[],[f69])).
% 0.20/0.42  fof(f71,plain,(
% 0.20/0.42    spl3_11),
% 0.20/0.42    inference(avatar_split_clause,[],[f16,f69])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 0.20/0.42  fof(f63,plain,(
% 0.20/0.42    spl3_9 | ~spl3_5 | ~spl3_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f58,f47,f43,f61])).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    spl3_5 <=> ! [X1,X0] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.42  fof(f47,plain,(
% 0.20/0.42    spl3_6 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl3_5 | ~spl3_6)),
% 0.20/0.42    inference(superposition,[],[f44,f48])).
% 0.20/0.42  fof(f48,plain,(
% 0.20/0.42    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl3_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f47])).
% 0.20/0.42  fof(f44,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) ) | ~spl3_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f43])).
% 0.20/0.42  fof(f57,plain,(
% 0.20/0.42    spl3_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f18,f55])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ( ! [X0] : (r2_hidden(sK0(X0),X0) | v1_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.20/0.42  fof(f49,plain,(
% 0.20/0.42    spl3_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f24,f47])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.42    inference(equality_resolution,[],[f23])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    spl3_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f20,f43])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.20/0.42  fof(f41,plain,(
% 0.20/0.42    spl3_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f15,f39])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.42  fof(f37,plain,(
% 0.20/0.42    spl3_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f14,f35])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.42    inference(cnf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    spl3_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f13,f31])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.42    inference(cnf_transformation,[],[f6])).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    ~spl3_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f12,f27])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.20/0.42    inference(flattening,[],[f8])).
% 0.20/0.42  fof(f8,negated_conjecture,(
% 0.20/0.42    ~k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.20/0.42    inference(negated_conjecture,[],[f7])).
% 0.20/0.42  fof(f7,conjecture,(
% 0.20/0.42    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_relat_1)).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (8990)------------------------------
% 0.20/0.42  % (8990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (8990)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (8990)Memory used [KB]: 10618
% 0.20/0.42  % (8990)Time elapsed: 0.006 s
% 0.20/0.42  % (8990)------------------------------
% 0.20/0.42  % (8990)------------------------------
% 0.20/0.42  % (8980)Success in time 0.07 s
%------------------------------------------------------------------------------
