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
% DateTime   : Thu Dec  3 12:45:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 107 expanded)
%              Number of leaves         :   16 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :  170 ( 260 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f43,f62,f67,f71,f83,f96,f106,f120,f126,f130])).

fof(f130,plain,
    ( ~ spl4_4
    | spl4_7
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | ~ spl4_4
    | spl4_7
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f128,f125])).

fof(f125,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl4_7
  <=> r1_tarski(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f128,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(resolution,[],[f102,f58])).

fof(f58,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl4_4
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f102,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(sK1,X1)
        | r1_tarski(sK1,k4_xboole_0(sK0,X1)) )
    | ~ spl4_10 ),
    inference(resolution,[],[f95,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f95,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_10
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f126,plain,
    ( ~ spl4_7
    | spl4_5
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f121,f104,f60,f69])).

fof(f60,plain,
    ( spl4_5
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f104,plain,
    ( spl4_11
  <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f121,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | spl4_5
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f82,f105])).

fof(f105,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f104])).

fof(f82,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f120,plain,
    ( spl4_4
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl4_4
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f118,f81])).

fof(f81,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f118,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl4_7 ),
    inference(resolution,[],[f75,f28])).

fof(f28,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f75,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k4_xboole_0(sK0,sK2),X0)
        | r1_xboole_0(sK1,X0) )
    | ~ spl4_7 ),
    inference(resolution,[],[f70,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f70,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f69])).

fof(f106,plain,
    ( spl4_11
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f44,f37,f104])).

fof(f37,plain,
    ( spl4_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f44,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl4_1 ),
    inference(resolution,[],[f38,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f96,plain,
    ( spl4_10
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f84,f65,f94])).

fof(f65,plain,
    ( spl4_6
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f84,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f66,f34])).

fof(f34,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f66,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f83,plain,
    ( ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f18,f60,f57])).

fof(f18,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,X2)
          <~> r1_tarski(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,X2)
            <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

fof(f71,plain,
    ( spl4_7
    | ~ spl4_1
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f63,f60,f37,f69])).

fof(f63,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl4_1
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f61,f44])).

fof(f61,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f67,plain,
    ( spl4_6
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f51,f41,f65])).

fof(f41,plain,
    ( spl4_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f51,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f50,f33])).

fof(f33,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f50,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(resolution,[],[f42,f32])).

% (10948)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f42,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f62,plain,
    ( spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f17,f60,f57])).

fof(f17,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f43,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f20,f41])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f39,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f19,f37])).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:51:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (10935)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (10941)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (10935)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f39,f43,f62,f67,f71,f83,f96,f106,f120,f126,f130])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    ~spl4_4 | spl4_7 | ~spl4_10),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f129])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    $false | (~spl4_4 | spl4_7 | ~spl4_10)),
% 0.21/0.48    inference(subsumption_resolution,[],[f128,f125])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    ~r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | spl4_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    spl4_7 <=> r1_tarski(sK1,k4_xboole_0(sK0,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | (~spl4_4 | ~spl4_10)),
% 0.21/0.48    inference(resolution,[],[f102,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    r1_xboole_0(sK1,sK2) | ~spl4_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    spl4_4 <=> r1_xboole_0(sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    ( ! [X1] : (~r1_xboole_0(sK1,X1) | r1_tarski(sK1,k4_xboole_0(sK0,X1))) ) | ~spl4_10),
% 0.21/0.48    inference(resolution,[],[f95,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    r1_tarski(sK1,sK0) | ~spl4_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f94])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    spl4_10 <=> r1_tarski(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    ~spl4_7 | spl4_5 | ~spl4_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f121,f104,f60,f69])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    spl4_5 <=> r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    spl4_11 <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    ~r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | (spl4_5 | ~spl4_11)),
% 0.21/0.48    inference(forward_demodulation,[],[f82,f105])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | ~spl4_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f104])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | spl4_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f60])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    spl4_4 | ~spl4_7),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f119])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    $false | (spl4_4 | ~spl4_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f118,f81])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ~r1_xboole_0(sK1,sK2) | spl4_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f57])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    r1_xboole_0(sK1,sK2) | ~spl4_7),
% 0.21/0.48    inference(resolution,[],[f75,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_xboole_0(k4_xboole_0(sK0,sK2),X0) | r1_xboole_0(sK1,X0)) ) | ~spl4_7),
% 0.21/0.48    inference(resolution,[],[f70,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | ~spl4_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f69])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    spl4_11 | ~spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f44,f37,f104])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    spl4_1 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | ~spl4_1),
% 0.21/0.48    inference(resolution,[],[f38,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f37])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    spl4_10 | ~spl4_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f84,f65,f94])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl4_6 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    r1_tarski(sK1,sK0) | ~spl4_6),
% 0.21/0.48    inference(resolution,[],[f66,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl4_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f65])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ~spl4_4 | ~spl4_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f18,f60,f57])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : ((r1_xboole_0(X1,X2) <~> r1_tarski(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f8])).
% 0.21/0.48  fof(f8,conjecture,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    spl4_7 | ~spl4_1 | ~spl4_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f63,f60,f37,f69])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | (~spl4_1 | ~spl4_5)),
% 0.21/0.48    inference(forward_demodulation,[],[f61,f44])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~spl4_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f60])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    spl4_6 | ~spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f51,f41,f65])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    spl4_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl4_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f50,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl4_2),
% 0.21/0.48    inference(resolution,[],[f42,f32])).
% 0.21/0.48  % (10948)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f41])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    spl4_4 | spl4_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f17,f60,f57])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    r1_tarski(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f20,f41])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f19,f37])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (10935)------------------------------
% 0.21/0.48  % (10935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (10935)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (10935)Memory used [KB]: 6140
% 0.21/0.48  % (10935)Time elapsed: 0.065 s
% 0.21/0.48  % (10935)------------------------------
% 0.21/0.48  % (10935)------------------------------
% 0.21/0.49  % (10933)Success in time 0.126 s
%------------------------------------------------------------------------------
