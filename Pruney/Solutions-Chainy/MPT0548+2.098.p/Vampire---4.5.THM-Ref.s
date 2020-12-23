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
% DateTime   : Thu Dec  3 12:49:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 (  64 expanded)
%              Number of leaves         :   14 (  24 expanded)
%              Depth                    :   12
%              Number of atoms          :  124 ( 144 expanded)
%              Number of equality atoms :   60 (  68 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f76,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f41,f45,f50,f72,f74])).

fof(f74,plain,
    ( spl1_1
    | ~ spl1_6 ),
    inference(avatar_contradiction_clause,[],[f73])).

fof(f73,plain,
    ( $false
    | spl1_1
    | ~ spl1_6 ),
    inference(subsumption_resolution,[],[f36,f71])).

fof(f71,plain,
    ( ! [X1] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X1)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl1_6
  <=> ! [X1] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f36,plain,
    ( k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl1_1
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f72,plain,
    ( ~ spl1_4
    | spl1_6
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f68,f48,f43,f39,f70,f48])).

fof(f39,plain,
    ( spl1_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f43,plain,
    ( spl1_3
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f48,plain,
    ( spl1_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f68,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k9_relat_1(k1_xboole_0,X1)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f60,f40])).

fof(f40,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f60,plain,
    ( ! [X1] :
        ( k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X1)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(superposition,[],[f24,f58])).

fof(f58,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(trivial_inequality_removal,[],[f57])).

fof(f57,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) )
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f56,f22])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f56,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
        | k1_xboole_0 != k4_xboole_0(k1_xboole_0,X0) )
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(resolution,[],[f55,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f55,plain,
    ( ! [X3] :
        ( ~ r1_xboole_0(k1_xboole_0,X3)
        | k1_xboole_0 = k7_relat_1(k1_xboole_0,X3) )
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f54,f44])).

fof(f44,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f54,plain,
    ( ! [X3] :
        ( ~ r1_xboole_0(k1_relat_1(k1_xboole_0),X3)
        | k1_xboole_0 = k7_relat_1(k1_xboole_0,X3) )
    | ~ spl1_4 ),
    inference(resolution,[],[f26,f49])).

fof(f49,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f50,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f46,f48])).

% (13556)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f46,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f23,f32])).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
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

fof(f23,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f45,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f20,f43])).

fof(f20,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f41,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f21,f39])).

fof(f21,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f37,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f19,f35])).

fof(f19,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f13])).

fof(f13,plain,
    ( ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:54:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (13569)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.45  % (13569)Refutation not found, incomplete strategy% (13569)------------------------------
% 0.20/0.45  % (13569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (13569)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.45  
% 0.20/0.45  % (13569)Memory used [KB]: 1535
% 0.20/0.45  % (13569)Time elapsed: 0.004 s
% 0.20/0.45  % (13569)------------------------------
% 0.20/0.45  % (13569)------------------------------
% 0.20/0.45  % (13559)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.45  % (13559)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f76,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f37,f41,f45,f50,f72,f74])).
% 0.20/0.45  fof(f74,plain,(
% 0.20/0.45    spl1_1 | ~spl1_6),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f73])).
% 0.20/0.45  fof(f73,plain,(
% 0.20/0.45    $false | (spl1_1 | ~spl1_6)),
% 0.20/0.45    inference(subsumption_resolution,[],[f36,f71])).
% 0.20/0.45  fof(f71,plain,(
% 0.20/0.45    ( ! [X1] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X1)) ) | ~spl1_6),
% 0.20/0.45    inference(avatar_component_clause,[],[f70])).
% 0.20/0.45  fof(f70,plain,(
% 0.20/0.45    spl1_6 <=> ! [X1] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) | spl1_1),
% 0.20/0.45    inference(avatar_component_clause,[],[f35])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    spl1_1 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.45  fof(f72,plain,(
% 0.20/0.45    ~spl1_4 | spl1_6 | ~spl1_2 | ~spl1_3 | ~spl1_4),
% 0.20/0.45    inference(avatar_split_clause,[],[f68,f48,f43,f39,f70,f48])).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    spl1_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.45  fof(f43,plain,(
% 0.20/0.45    spl1_3 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.20/0.45  fof(f48,plain,(
% 0.20/0.45    spl1_4 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.20/0.45  fof(f68,plain,(
% 0.20/0.45    ( ! [X1] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X1) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_2 | ~spl1_3 | ~spl1_4)),
% 0.20/0.45    inference(forward_demodulation,[],[f60,f40])).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_2),
% 0.20/0.45    inference(avatar_component_clause,[],[f39])).
% 0.20/0.45  fof(f60,plain,(
% 0.20/0.45    ( ! [X1] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X1) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_3 | ~spl1_4)),
% 0.20/0.45    inference(superposition,[],[f24,f58])).
% 0.20/0.45  fof(f58,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | (~spl1_3 | ~spl1_4)),
% 0.20/0.45    inference(trivial_inequality_removal,[],[f57])).
% 0.20/0.45  fof(f57,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | (~spl1_3 | ~spl1_4)),
% 0.20/0.45    inference(forward_demodulation,[],[f56,f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.20/0.45  fof(f56,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) | k1_xboole_0 != k4_xboole_0(k1_xboole_0,X0)) ) | (~spl1_3 | ~spl1_4)),
% 0.20/0.45    inference(resolution,[],[f55,f28])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.45    inference(nnf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.45  fof(f55,plain,(
% 0.20/0.45    ( ! [X3] : (~r1_xboole_0(k1_xboole_0,X3) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X3)) ) | (~spl1_3 | ~spl1_4)),
% 0.20/0.45    inference(forward_demodulation,[],[f54,f44])).
% 0.20/0.45  fof(f44,plain,(
% 0.20/0.45    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_3),
% 0.20/0.45    inference(avatar_component_clause,[],[f43])).
% 0.20/0.45  fof(f54,plain,(
% 0.20/0.45    ( ! [X3] : (~r1_xboole_0(k1_relat_1(k1_xboole_0),X3) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X3)) ) | ~spl1_4),
% 0.20/0.45    inference(resolution,[],[f26,f49])).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    v1_relat_1(k1_xboole_0) | ~spl1_4),
% 0.20/0.45    inference(avatar_component_clause,[],[f48])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.45    inference(nnf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,axiom,(
% 0.20/0.45    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.45  fof(f50,plain,(
% 0.20/0.45    spl1_4),
% 0.20/0.45    inference(avatar_split_clause,[],[f46,f48])).
% 0.20/0.45  % (13556)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    v1_relat_1(k1_xboole_0)),
% 0.20/0.45    inference(superposition,[],[f23,f32])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.45    inference(equality_resolution,[],[f31])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.45    inference(cnf_transformation,[],[f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.45    inference(flattening,[],[f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.45    inference(nnf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.45  fof(f45,plain,(
% 0.20/0.45    spl1_3),
% 0.20/0.45    inference(avatar_split_clause,[],[f20,f43])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.45    inference(cnf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    spl1_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f21,f39])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.45    inference(cnf_transformation,[],[f6])).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    ~spl1_1),
% 0.20/0.45    inference(avatar_split_clause,[],[f19,f35])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f13])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 0.20/0.45    inference(ennf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,negated_conjecture,(
% 0.20/0.45    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.20/0.45    inference(negated_conjecture,[],[f8])).
% 0.20/0.45  fof(f8,conjecture,(
% 0.20/0.45    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (13559)------------------------------
% 0.20/0.45  % (13559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (13559)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (13559)Memory used [KB]: 10618
% 0.20/0.45  % (13559)Time elapsed: 0.005 s
% 0.20/0.45  % (13559)------------------------------
% 0.20/0.45  % (13559)------------------------------
% 0.20/0.45  % (13556)Refutation not found, incomplete strategy% (13556)------------------------------
% 0.20/0.45  % (13556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (13556)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.45  
% 0.20/0.45  % (13556)Memory used [KB]: 10490
% 0.20/0.45  % (13556)Time elapsed: 0.004 s
% 0.20/0.45  % (13556)------------------------------
% 0.20/0.45  % (13556)------------------------------
% 0.20/0.45  % (13549)Success in time 0.098 s
%------------------------------------------------------------------------------
