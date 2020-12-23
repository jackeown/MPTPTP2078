%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   59 (  83 expanded)
%              Number of leaves         :   15 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :  154 ( 210 expanded)
%              Number of equality atoms :    5 (   7 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f42,f47,f57,f74,f80,f83,f86])).

fof(f86,plain,
    ( ~ spl3_4
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f84,f46])).

fof(f46,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f84,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_9 ),
    inference(resolution,[],[f73,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f73,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl3_9
  <=> r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f83,plain,
    ( ~ spl3_4
    | spl3_8 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | ~ spl3_4
    | spl3_8 ),
    inference(subsumption_resolution,[],[f81,f46])).

fof(f81,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_8 ),
    inference(resolution,[],[f69,f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f69,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_8
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f80,plain,
    ( ~ spl3_4
    | spl3_7 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | ~ spl3_4
    | spl3_7 ),
    inference(subsumption_resolution,[],[f78,f46])).

fof(f78,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_7 ),
    inference(resolution,[],[f65,f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

% (9435)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f65,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_7
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f74,plain,
    ( ~ spl3_7
    | ~ spl3_8
    | spl3_9
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f61,f54,f39,f34,f29,f71,f67,f63])).

fof(f29,plain,
    ( spl3_1
  <=> v5_funct_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f34,plain,
    ( spl3_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f39,plain,
    ( spl3_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f54,plain,
    ( spl3_6
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f61,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f60,f56])).

fof(f56,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f60,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f59,f41])).

fof(f41,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f59,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK0)
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f58,f36])).

fof(f36,plain,
    ( v1_funct_1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f58,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK0)
    | spl3_1 ),
    inference(resolution,[],[f24,f31])).

fof(f31,plain,
    ( ~ v5_funct_1(k1_xboole_0,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v5_funct_1(X1,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | r2_hidden(sK1(X0,X1),k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

fof(f57,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f19,f54])).

fof(f19,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f47,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f18,f44])).

fof(f18,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f42,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f15,f39])).

fof(f15,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => v5_funct_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v5_funct_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

fof(f37,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f16,f34])).

fof(f16,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f32,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f17,f29])).

fof(f17,plain,(
    ~ v5_funct_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:22:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (9438)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.43  % (9431)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.43  % (9432)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.43  % (9432)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f87,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f32,f37,f42,f47,f57,f74,f80,f83,f86])).
% 0.22/0.43  fof(f86,plain,(
% 0.22/0.43    ~spl3_4 | ~spl3_9),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f85])).
% 0.22/0.43  fof(f85,plain,(
% 0.22/0.43    $false | (~spl3_4 | ~spl3_9)),
% 0.22/0.43    inference(subsumption_resolution,[],[f84,f46])).
% 0.22/0.43  fof(f46,plain,(
% 0.22/0.43    v1_xboole_0(k1_xboole_0) | ~spl3_4),
% 0.22/0.43    inference(avatar_component_clause,[],[f44])).
% 0.22/0.43  fof(f44,plain,(
% 0.22/0.43    spl3_4 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.43  fof(f84,plain,(
% 0.22/0.43    ~v1_xboole_0(k1_xboole_0) | ~spl3_9),
% 0.22/0.43    inference(resolution,[],[f73,f27])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.43  fof(f73,plain,(
% 0.22/0.43    r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0) | ~spl3_9),
% 0.22/0.43    inference(avatar_component_clause,[],[f71])).
% 0.22/0.43  fof(f71,plain,(
% 0.22/0.43    spl3_9 <=> r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.43  fof(f83,plain,(
% 0.22/0.43    ~spl3_4 | spl3_8),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f82])).
% 0.22/0.43  fof(f82,plain,(
% 0.22/0.43    $false | (~spl3_4 | spl3_8)),
% 0.22/0.43    inference(subsumption_resolution,[],[f81,f46])).
% 0.22/0.43  fof(f81,plain,(
% 0.22/0.43    ~v1_xboole_0(k1_xboole_0) | spl3_8),
% 0.22/0.43    inference(resolution,[],[f69,f22])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.22/0.43  fof(f69,plain,(
% 0.22/0.43    ~v1_relat_1(k1_xboole_0) | spl3_8),
% 0.22/0.43    inference(avatar_component_clause,[],[f67])).
% 0.22/0.43  fof(f67,plain,(
% 0.22/0.43    spl3_8 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.43  fof(f80,plain,(
% 0.22/0.43    ~spl3_4 | spl3_7),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f79])).
% 0.22/0.43  fof(f79,plain,(
% 0.22/0.43    $false | (~spl3_4 | spl3_7)),
% 0.22/0.43    inference(subsumption_resolution,[],[f78,f46])).
% 0.22/0.43  fof(f78,plain,(
% 0.22/0.43    ~v1_xboole_0(k1_xboole_0) | spl3_7),
% 0.22/0.43    inference(resolution,[],[f65,f21])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f5])).
% 0.22/0.43  % (9435)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).
% 0.22/0.43  fof(f65,plain,(
% 0.22/0.43    ~v1_funct_1(k1_xboole_0) | spl3_7),
% 0.22/0.43    inference(avatar_component_clause,[],[f63])).
% 0.22/0.43  fof(f63,plain,(
% 0.22/0.43    spl3_7 <=> v1_funct_1(k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.43  fof(f74,plain,(
% 0.22/0.43    ~spl3_7 | ~spl3_8 | spl3_9 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f61,f54,f39,f34,f29,f71,f67,f63])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    spl3_1 <=> v5_funct_1(k1_xboole_0,sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    spl3_2 <=> v1_funct_1(sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    spl3_3 <=> v1_relat_1(sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.43  fof(f54,plain,(
% 0.22/0.43    spl3_6 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.43  fof(f61,plain,(
% 0.22/0.43    r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_6)),
% 0.22/0.43    inference(forward_demodulation,[],[f60,f56])).
% 0.22/0.43  fof(f56,plain,(
% 0.22/0.43    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_6),
% 0.22/0.43    inference(avatar_component_clause,[],[f54])).
% 0.22/0.43  fof(f60,plain,(
% 0.22/0.43    ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | (spl3_1 | ~spl3_2 | ~spl3_3)),
% 0.22/0.43    inference(subsumption_resolution,[],[f59,f41])).
% 0.22/0.43  fof(f41,plain,(
% 0.22/0.43    v1_relat_1(sK0) | ~spl3_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f39])).
% 0.22/0.43  fof(f59,plain,(
% 0.22/0.43    ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(sK0) | (spl3_1 | ~spl3_2)),
% 0.22/0.43    inference(subsumption_resolution,[],[f58,f36])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    v1_funct_1(sK0) | ~spl3_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f34])).
% 0.22/0.43  fof(f58,plain,(
% 0.22/0.43    ~v1_funct_1(sK0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(sK0) | spl3_1),
% 0.22/0.43    inference(resolution,[],[f24,f31])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    ~v5_funct_1(k1_xboole_0,sK0) | spl3_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f29])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    ( ! [X0,X1] : (v5_funct_1(X1,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.43    inference(flattening,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,axiom,(
% 0.22/0.43    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).
% 0.22/0.43  fof(f57,plain,(
% 0.22/0.43    spl3_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f19,f54])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.44    inference(cnf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.44  fof(f47,plain,(
% 0.22/0.44    spl3_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f18,f44])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    v1_xboole_0(k1_xboole_0)),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    v1_xboole_0(k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    spl3_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f15,f39])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    v1_relat_1(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.44    inference(flattening,[],[f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,negated_conjecture,(
% 0.22/0.44    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.22/0.44    inference(negated_conjecture,[],[f7])).
% 0.22/0.44  fof(f7,conjecture,(
% 0.22/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    spl3_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f16,f34])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    v1_funct_1(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    ~spl3_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f17,f29])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ~v5_funct_1(k1_xboole_0,sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (9432)------------------------------
% 0.22/0.44  % (9432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (9432)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (9432)Memory used [KB]: 10618
% 0.22/0.44  % (9432)Time elapsed: 0.006 s
% 0.22/0.44  % (9432)------------------------------
% 0.22/0.44  % (9432)------------------------------
% 0.22/0.44  % (9433)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.22/0.44  % (9430)Success in time 0.073 s
%------------------------------------------------------------------------------
