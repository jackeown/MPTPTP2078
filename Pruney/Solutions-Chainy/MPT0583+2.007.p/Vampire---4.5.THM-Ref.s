%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  46 expanded)
%              Number of leaves         :    8 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   75 ( 110 expanded)
%              Number of equality atoms :   16 (  26 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f43,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f18,f23,f28,f33,f38,f42])).

fof(f42,plain,
    ( spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f41])).

fof(f41,plain,
    ( $false
    | spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f39,f22])).

fof(f22,plain,
    ( k1_xboole_0 != k7_relat_1(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl2_2
  <=> k1_xboole_0 = k7_relat_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f39,plain,
    ( k1_xboole_0 = k7_relat_1(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(resolution,[],[f37,f27])).

fof(f27,plain,
    ( r1_xboole_0(sK1,k1_relat_1(sK0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl2_3
  <=> r1_xboole_0(sK1,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f37,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k1_relat_1(sK0))
        | k1_xboole_0 = k7_relat_1(sK0,X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl2_5
  <=> ! [X0] :
        ( k1_xboole_0 = k7_relat_1(sK0,X0)
        | ~ r1_xboole_0(X0,k1_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f38,plain,
    ( spl2_5
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f34,f31,f36])).

fof(f31,plain,
    ( spl2_4
  <=> ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK0),X0)
        | k1_xboole_0 = k7_relat_1(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f34,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k7_relat_1(sK0,X0)
        | ~ r1_xboole_0(X0,k1_relat_1(sK0)) )
    | ~ spl2_4 ),
    inference(resolution,[],[f32,f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f32,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK0),X0)
        | k1_xboole_0 = k7_relat_1(sK0,X0) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f31])).

fof(f33,plain,
    ( spl2_4
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f29,f15,f31])).

fof(f15,plain,
    ( spl2_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f29,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK0),X0)
        | k1_xboole_0 = k7_relat_1(sK0,X0) )
    | ~ spl2_1 ),
    inference(resolution,[],[f11,f17])).

fof(f17,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f15])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ( k7_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k7_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f28,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f8,f25])).

fof(f8,plain,(
    r1_xboole_0(sK1,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k7_relat_1(X0,X1)
          & r1_xboole_0(X1,k1_relat_1(X0)) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( r1_xboole_0(X1,k1_relat_1(X0))
           => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(f23,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f9,f20])).

fof(f9,plain,(
    k1_xboole_0 != k7_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f5])).

fof(f18,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f10,f15])).

fof(f10,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f5])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n007.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:28:51 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.39  % (18890)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.40  % (18882)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.41  % (18882)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f43,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(avatar_sat_refutation,[],[f18,f23,f28,f33,f38,f42])).
% 0.20/0.41  fof(f42,plain,(
% 0.20/0.41    spl2_2 | ~spl2_3 | ~spl2_5),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f41])).
% 0.20/0.41  fof(f41,plain,(
% 0.20/0.41    $false | (spl2_2 | ~spl2_3 | ~spl2_5)),
% 0.20/0.41    inference(subsumption_resolution,[],[f39,f22])).
% 0.20/0.41  fof(f22,plain,(
% 0.20/0.41    k1_xboole_0 != k7_relat_1(sK0,sK1) | spl2_2),
% 0.20/0.41    inference(avatar_component_clause,[],[f20])).
% 0.20/0.41  fof(f20,plain,(
% 0.20/0.41    spl2_2 <=> k1_xboole_0 = k7_relat_1(sK0,sK1)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.41  fof(f39,plain,(
% 0.20/0.41    k1_xboole_0 = k7_relat_1(sK0,sK1) | (~spl2_3 | ~spl2_5)),
% 0.20/0.41    inference(resolution,[],[f37,f27])).
% 0.20/0.41  fof(f27,plain,(
% 0.20/0.41    r1_xboole_0(sK1,k1_relat_1(sK0)) | ~spl2_3),
% 0.20/0.41    inference(avatar_component_clause,[],[f25])).
% 0.20/0.41  fof(f25,plain,(
% 0.20/0.41    spl2_3 <=> r1_xboole_0(sK1,k1_relat_1(sK0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.41  fof(f37,plain,(
% 0.20/0.41    ( ! [X0] : (~r1_xboole_0(X0,k1_relat_1(sK0)) | k1_xboole_0 = k7_relat_1(sK0,X0)) ) | ~spl2_5),
% 0.20/0.41    inference(avatar_component_clause,[],[f36])).
% 0.20/0.41  fof(f36,plain,(
% 0.20/0.41    spl2_5 <=> ! [X0] : (k1_xboole_0 = k7_relat_1(sK0,X0) | ~r1_xboole_0(X0,k1_relat_1(sK0)))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.41  fof(f38,plain,(
% 0.20/0.41    spl2_5 | ~spl2_4),
% 0.20/0.41    inference(avatar_split_clause,[],[f34,f31,f36])).
% 0.20/0.41  fof(f31,plain,(
% 0.20/0.41    spl2_4 <=> ! [X0] : (~r1_xboole_0(k1_relat_1(sK0),X0) | k1_xboole_0 = k7_relat_1(sK0,X0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.41  fof(f34,plain,(
% 0.20/0.41    ( ! [X0] : (k1_xboole_0 = k7_relat_1(sK0,X0) | ~r1_xboole_0(X0,k1_relat_1(sK0))) ) | ~spl2_4),
% 0.20/0.41    inference(resolution,[],[f32,f13])).
% 0.20/0.41  fof(f13,plain,(
% 0.20/0.41    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f7])).
% 0.20/0.41  fof(f7,plain,(
% 0.20/0.41    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.41  fof(f32,plain,(
% 0.20/0.41    ( ! [X0] : (~r1_xboole_0(k1_relat_1(sK0),X0) | k1_xboole_0 = k7_relat_1(sK0,X0)) ) | ~spl2_4),
% 0.20/0.41    inference(avatar_component_clause,[],[f31])).
% 0.20/0.41  fof(f33,plain,(
% 0.20/0.41    spl2_4 | ~spl2_1),
% 0.20/0.41    inference(avatar_split_clause,[],[f29,f15,f31])).
% 0.20/0.41  fof(f15,plain,(
% 0.20/0.41    spl2_1 <=> v1_relat_1(sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.41  fof(f29,plain,(
% 0.20/0.41    ( ! [X0] : (~r1_xboole_0(k1_relat_1(sK0),X0) | k1_xboole_0 = k7_relat_1(sK0,X0)) ) | ~spl2_1),
% 0.20/0.41    inference(resolution,[],[f11,f17])).
% 0.20/0.41  fof(f17,plain,(
% 0.20/0.41    v1_relat_1(sK0) | ~spl2_1),
% 0.20/0.41    inference(avatar_component_clause,[],[f15])).
% 0.20/0.41  fof(f11,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = k1_xboole_0) )),
% 0.20/0.41    inference(cnf_transformation,[],[f6])).
% 0.20/0.41  fof(f6,plain,(
% 0.20/0.41    ! [X0,X1] : ((k7_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    ! [X0,X1] : (v1_relat_1(X1) => (k7_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.20/0.41  fof(f28,plain,(
% 0.20/0.41    spl2_3),
% 0.20/0.41    inference(avatar_split_clause,[],[f8,f25])).
% 0.20/0.41  fof(f8,plain,(
% 0.20/0.41    r1_xboole_0(sK1,k1_relat_1(sK0))),
% 0.20/0.41    inference(cnf_transformation,[],[f5])).
% 0.20/0.41  fof(f5,plain,(
% 0.20/0.41    ? [X0] : (? [X1] : (k1_xboole_0 != k7_relat_1(X0,X1) & r1_xboole_0(X1,k1_relat_1(X0))) & v1_relat_1(X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f4])).
% 0.20/0.41  fof(f4,negated_conjecture,(
% 0.20/0.41    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 0.20/0.41    inference(negated_conjecture,[],[f3])).
% 0.20/0.41  fof(f3,conjecture,(
% 0.20/0.41    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).
% 0.20/0.41  fof(f23,plain,(
% 0.20/0.41    ~spl2_2),
% 0.20/0.41    inference(avatar_split_clause,[],[f9,f20])).
% 0.20/0.41  fof(f9,plain,(
% 0.20/0.41    k1_xboole_0 != k7_relat_1(sK0,sK1)),
% 0.20/0.41    inference(cnf_transformation,[],[f5])).
% 0.20/0.41  fof(f18,plain,(
% 0.20/0.41    spl2_1),
% 0.20/0.41    inference(avatar_split_clause,[],[f10,f15])).
% 0.20/0.41  fof(f10,plain,(
% 0.20/0.41    v1_relat_1(sK0)),
% 0.20/0.41    inference(cnf_transformation,[],[f5])).
% 0.20/0.41  % SZS output end Proof for theBenchmark
% 0.20/0.41  % (18882)------------------------------
% 0.20/0.41  % (18882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (18882)Termination reason: Refutation
% 0.20/0.41  
% 0.20/0.41  % (18882)Memory used [KB]: 10490
% 0.20/0.41  % (18882)Time elapsed: 0.005 s
% 0.20/0.41  % (18882)------------------------------
% 0.20/0.41  % (18882)------------------------------
% 0.20/0.41  % (18880)Success in time 0.062 s
%------------------------------------------------------------------------------
