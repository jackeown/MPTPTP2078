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
% DateTime   : Thu Dec  3 12:42:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 108 expanded)
%              Number of leaves         :   15 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :  153 ( 279 expanded)
%              Number of equality atoms :   33 (  92 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f104,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f36,f41,f46,f60,f69,f75,f86,f91,f98,f103])).

fof(f103,plain,
    ( spl4_2
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | spl4_2
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f35,f56,f15])).

fof(f15,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f56,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl4_5
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f35,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f98,plain,
    ( spl4_8
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f97,f84,f72])).

fof(f72,plain,
    ( spl4_8
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f84,plain,
    ( spl4_10
  <=> ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f97,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_10 ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0)
    | ~ spl4_10 ),
    inference(resolution,[],[f93,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f93,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(X1,sK0),sK1)
        | r1_tarski(X1,sK0) )
    | ~ spl4_10 ),
    inference(resolution,[],[f85,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f85,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f84])).

fof(f91,plain,
    ( spl4_1
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f87])).

fof(f87,plain,
    ( $false
    | spl4_1
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f30,f82,f15])).

fof(f82,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_9
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f30,plain,
    ( k1_xboole_0 != sK0
    | spl4_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl4_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f86,plain,
    ( spl4_9
    | spl4_10
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f52,f43,f84,f81])).

fof(f43,plain,
    ( spl4_4
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f48,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f48,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X3,sK0) )
    | ~ spl4_4 ),
    inference(superposition,[],[f23,f45])).

fof(f45,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f75,plain,
    ( spl4_3
    | ~ spl4_8
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f70,f66,f72,f38])).

fof(f38,plain,
    ( spl4_3
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f66,plain,
    ( spl4_7
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f70,plain,
    ( ~ r1_tarski(sK1,sK0)
    | sK0 = sK1
    | ~ spl4_7 ),
    inference(resolution,[],[f68,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f68,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f69,plain,
    ( spl4_7
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f64,f58,f66])).

fof(f58,plain,
    ( spl4_6
  <=> ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f64,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_6 ),
    inference(duplicate_literal_removal,[],[f62])).

fof(f62,plain,
    ( r1_tarski(sK0,sK1)
    | r1_tarski(sK0,sK1)
    | ~ spl4_6 ),
    inference(resolution,[],[f61,f20])).

fof(f61,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(X0,sK1),sK0)
        | r1_tarski(X0,sK1) )
    | ~ spl4_6 ),
    inference(resolution,[],[f59,f21])).

fof(f59,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f60,plain,
    ( spl4_5
    | spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f50,f43,f58,f55])).

fof(f50,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f47,f24])).

fof(f47,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X0,sK1) )
    | ~ spl4_4 ),
    inference(superposition,[],[f22,f45])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f46,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f11,f43])).

fof(f11,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).

fof(f41,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f14,f38])).

fof(f14,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f36,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f13,f33])).

fof(f13,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f31,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f12,f28])).

fof(f12,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:00:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (2506)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (2498)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (2505)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.52  % (2490)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (2497)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (2506)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f31,f36,f41,f46,f60,f69,f75,f86,f91,f98,f103])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    spl4_2 | ~spl4_5),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f99])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    $false | (spl4_2 | ~spl4_5)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f35,f56,f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl4_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f55])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    spl4_5 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    k1_xboole_0 != sK1 | spl4_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    spl4_2 <=> k1_xboole_0 = sK1),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    spl4_8 | ~spl4_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f97,f84,f72])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    spl4_8 <=> r1_tarski(sK1,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    spl4_10 <=> ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    r1_tarski(sK1,sK0) | ~spl4_10),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f95])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0) | ~spl4_10),
% 0.22/0.52    inference(resolution,[],[f93,f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    ( ! [X1] : (~r2_hidden(sK3(X1,sK0),sK1) | r1_tarski(X1,sK0)) ) | ~spl4_10),
% 0.22/0.52    inference(resolution,[],[f85,f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1)) ) | ~spl4_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f84])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    spl4_1 | ~spl4_9),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f87])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    $false | (spl4_1 | ~spl4_9)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f30,f82,f15])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl4_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f81])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    spl4_9 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    k1_xboole_0 != sK0 | spl4_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    spl4_1 <=> k1_xboole_0 = sK0),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    spl4_9 | spl4_10 | ~spl4_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f52,f43,f84,f81])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    spl4_4 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0)) ) | ~spl4_4),
% 0.22/0.52    inference(resolution,[],[f48,f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X3,sK0)) ) | ~spl4_4),
% 0.22/0.52    inference(superposition,[],[f23,f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) | ~spl4_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f43])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    spl4_3 | ~spl4_8 | ~spl4_7),
% 0.22/0.52    inference(avatar_split_clause,[],[f70,f66,f72,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    spl4_3 <=> sK0 = sK1),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    spl4_7 <=> r1_tarski(sK0,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ~r1_tarski(sK1,sK0) | sK0 = sK1 | ~spl4_7),
% 0.22/0.52    inference(resolution,[],[f68,f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    r1_tarski(sK0,sK1) | ~spl4_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f66])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    spl4_7 | ~spl4_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f64,f58,f66])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    spl4_6 <=> ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    r1_tarski(sK0,sK1) | ~spl4_6),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    r1_tarski(sK0,sK1) | r1_tarski(sK0,sK1) | ~spl4_6),
% 0.22/0.52    inference(resolution,[],[f61,f20])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(sK3(X0,sK1),sK0) | r1_tarski(X0,sK1)) ) | ~spl4_6),
% 0.22/0.52    inference(resolution,[],[f59,f21])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl4_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f58])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    spl4_5 | spl4_6 | ~spl4_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f50,f43,f58,f55])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(X0,sK1) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl4_4),
% 0.22/0.52    inference(resolution,[],[f47,f24])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X0,sK1)) ) | ~spl4_4),
% 0.22/0.52    inference(superposition,[],[f22,f45])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    spl4_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f11,f43])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 0.22/0.52    inference(flattening,[],[f7])).
% 0.22/0.52  fof(f7,plain,(
% 0.22/0.52    ? [X0,X1] : ((X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.52    inference(negated_conjecture,[],[f5])).
% 0.22/0.52  fof(f5,conjecture,(
% 0.22/0.52    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ~spl4_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f14,f38])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    sK0 != sK1),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ~spl4_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f13,f33])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    k1_xboole_0 != sK1),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ~spl4_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f12,f28])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    k1_xboole_0 != sK0),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (2506)------------------------------
% 0.22/0.52  % (2506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (2506)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (2506)Memory used [KB]: 10746
% 0.22/0.52  % (2506)Time elapsed: 0.065 s
% 0.22/0.52  % (2506)------------------------------
% 0.22/0.52  % (2506)------------------------------
% 0.22/0.52  % (2505)Refutation not found, incomplete strategy% (2505)------------------------------
% 0.22/0.52  % (2505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (2482)Success in time 0.161 s
%------------------------------------------------------------------------------
