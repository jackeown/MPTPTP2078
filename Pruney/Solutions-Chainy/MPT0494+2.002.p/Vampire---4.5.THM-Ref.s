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
% DateTime   : Thu Dec  3 12:48:22 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 113 expanded)
%              Number of leaves         :   20 (  51 expanded)
%              Depth                    :    7
%              Number of atoms          :  217 ( 339 expanded)
%              Number of equality atoms :   16 (  24 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f157,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f39,f43,f47,f51,f55,f59,f74,f86,f113,f148,f155])).

fof(f155,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_17
    | ~ spl3_23 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_17
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f153,f112])).

fof(f112,plain,
    ( ! [X3] : v1_relat_1(k7_relat_1(sK1,X3))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl3_17
  <=> ! [X3] : v1_relat_1(k7_relat_1(sK1,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f153,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f152,f38])).

fof(f38,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f152,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f149,f33])).

fof(f33,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl3_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f149,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl3_1
    | ~ spl3_23 ),
    inference(resolution,[],[f147,f28])).

fof(f28,plain,
    ( ~ r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),sK2),k5_relat_1(sK1,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl3_1
  <=> r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),sK2),k5_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f147,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k5_relat_1(k7_relat_1(X0,X1),X2),k5_relat_1(X0,X2))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k7_relat_1(X0,X1)) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl3_23
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k5_relat_1(k7_relat_1(X0,X1),X2),k5_relat_1(X0,X2))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k7_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f148,plain,
    ( spl3_23
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f144,f53,f41,f146])).

fof(f41,plain,
    ( spl3_4
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f53,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( r1_tarski(k7_relat_1(X1,X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f144,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k5_relat_1(k7_relat_1(X0,X1),X2),k5_relat_1(X0,X2))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k7_relat_1(X0,X1)) )
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(duplicate_literal_removal,[],[f143])).

fof(f143,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k5_relat_1(k7_relat_1(X0,X1),X2),k5_relat_1(X0,X2))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(resolution,[],[f42,f54])).

fof(f54,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k7_relat_1(X1,X0),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f53])).

fof(f42,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f113,plain,
    ( spl3_17
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f109,f84,f49,f36,f111])).

fof(f49,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( v1_relat_1(k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f84,plain,
    ( spl3_12
  <=> ! [X1] : k7_relat_1(sK1,X1) = k3_xboole_0(sK1,k7_relat_1(sK1,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f109,plain,
    ( ! [X3] : v1_relat_1(k7_relat_1(sK1,X3))
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f108,f38])).

fof(f108,plain,
    ( ! [X3] :
        ( v1_relat_1(k7_relat_1(sK1,X3))
        | ~ v1_relat_1(sK1) )
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(superposition,[],[f50,f85])).

fof(f85,plain,
    ( ! [X1] : k7_relat_1(sK1,X1) = k3_xboole_0(sK1,k7_relat_1(sK1,X1))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f84])).

fof(f50,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f49])).

fof(f86,plain,
    ( spl3_12
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f76,f72,f36,f84])).

fof(f72,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( k7_relat_1(X0,X1) = k3_xboole_0(X0,k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f76,plain,
    ( ! [X1] : k7_relat_1(sK1,X1) = k3_xboole_0(sK1,k7_relat_1(sK1,X1))
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(resolution,[],[f73,f38])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k7_relat_1(X0,X1) = k3_xboole_0(X0,k7_relat_1(X0,X1)) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f72])).

fof(f74,plain,
    ( spl3_10
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f70,f57,f53,f45,f72])).

fof(f45,plain,
    ( spl3_5
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f57,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X0,X1) = k3_xboole_0(X0,k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f69,f46])).

fof(f46,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X0,X1) = k3_xboole_0(k7_relat_1(X0,X1),X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(resolution,[],[f58,f54])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f59,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f24,f57])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f55,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f23,f53])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f51,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f22,f49])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f47,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f21,f45])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f43,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f20,f41])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relat_1)).

fof(f39,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f17,f36])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),sK2),k5_relat_1(sK1,sK2))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f15,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),X2),k5_relat_1(sK1,X2))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),X2),k5_relat_1(sK1,X2))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),sK2),k5_relat_1(sK1,sK2))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_relat_1)).

fof(f34,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f18,f31])).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f19,f26])).

fof(f19,plain,(
    ~ r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),sK2),k5_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n002.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 12:46:36 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.19/0.39  % (30563)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.19/0.39  % (30562)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.19/0.39  % (30563)Refutation found. Thanks to Tanya!
% 0.19/0.39  % SZS status Theorem for theBenchmark
% 0.19/0.39  % SZS output start Proof for theBenchmark
% 0.19/0.39  fof(f157,plain,(
% 0.19/0.39    $false),
% 0.19/0.39    inference(avatar_sat_refutation,[],[f29,f34,f39,f43,f47,f51,f55,f59,f74,f86,f113,f148,f155])).
% 0.19/0.39  fof(f155,plain,(
% 0.19/0.39    spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_17 | ~spl3_23),
% 0.19/0.39    inference(avatar_contradiction_clause,[],[f154])).
% 0.19/0.39  fof(f154,plain,(
% 0.19/0.39    $false | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_17 | ~spl3_23)),
% 0.19/0.39    inference(subsumption_resolution,[],[f153,f112])).
% 0.19/0.39  fof(f112,plain,(
% 0.19/0.39    ( ! [X3] : (v1_relat_1(k7_relat_1(sK1,X3))) ) | ~spl3_17),
% 0.19/0.39    inference(avatar_component_clause,[],[f111])).
% 0.19/0.39  fof(f111,plain,(
% 0.19/0.39    spl3_17 <=> ! [X3] : v1_relat_1(k7_relat_1(sK1,X3))),
% 0.19/0.39    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.19/0.39  fof(f153,plain,(
% 0.19/0.39    ~v1_relat_1(k7_relat_1(sK1,sK0)) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_23)),
% 0.19/0.39    inference(subsumption_resolution,[],[f152,f38])).
% 0.19/0.39  fof(f38,plain,(
% 0.19/0.39    v1_relat_1(sK1) | ~spl3_3),
% 0.19/0.39    inference(avatar_component_clause,[],[f36])).
% 0.19/0.39  fof(f36,plain,(
% 0.19/0.39    spl3_3 <=> v1_relat_1(sK1)),
% 0.19/0.39    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.39  fof(f152,plain,(
% 0.19/0.39    ~v1_relat_1(sK1) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | (spl3_1 | ~spl3_2 | ~spl3_23)),
% 0.19/0.39    inference(subsumption_resolution,[],[f149,f33])).
% 0.19/0.39  fof(f33,plain,(
% 0.19/0.39    v1_relat_1(sK2) | ~spl3_2),
% 0.19/0.39    inference(avatar_component_clause,[],[f31])).
% 0.19/0.39  fof(f31,plain,(
% 0.19/0.39    spl3_2 <=> v1_relat_1(sK2)),
% 0.19/0.39    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.39  fof(f149,plain,(
% 0.19/0.39    ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | (spl3_1 | ~spl3_23)),
% 0.19/0.39    inference(resolution,[],[f147,f28])).
% 0.19/0.39  fof(f28,plain,(
% 0.19/0.39    ~r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),sK2),k5_relat_1(sK1,sK2)) | spl3_1),
% 0.19/0.39    inference(avatar_component_clause,[],[f26])).
% 0.19/0.39  fof(f26,plain,(
% 0.19/0.39    spl3_1 <=> r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),sK2),k5_relat_1(sK1,sK2))),
% 0.19/0.39    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.39  fof(f147,plain,(
% 0.19/0.39    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(k7_relat_1(X0,X1),X2),k5_relat_1(X0,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X0) | ~v1_relat_1(k7_relat_1(X0,X1))) ) | ~spl3_23),
% 0.19/0.39    inference(avatar_component_clause,[],[f146])).
% 0.19/0.39  fof(f146,plain,(
% 0.19/0.39    spl3_23 <=> ! [X1,X0,X2] : (r1_tarski(k5_relat_1(k7_relat_1(X0,X1),X2),k5_relat_1(X0,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X0) | ~v1_relat_1(k7_relat_1(X0,X1)))),
% 0.19/0.39    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.19/0.39  fof(f148,plain,(
% 0.19/0.39    spl3_23 | ~spl3_4 | ~spl3_7),
% 0.19/0.39    inference(avatar_split_clause,[],[f144,f53,f41,f146])).
% 0.19/0.39  fof(f41,plain,(
% 0.19/0.39    spl3_4 <=> ! [X1,X0,X2] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.19/0.39    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.39  fof(f53,plain,(
% 0.19/0.39    spl3_7 <=> ! [X1,X0] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.19/0.39    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.19/0.39  fof(f144,plain,(
% 0.19/0.39    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(k7_relat_1(X0,X1),X2),k5_relat_1(X0,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X0) | ~v1_relat_1(k7_relat_1(X0,X1))) ) | (~spl3_4 | ~spl3_7)),
% 0.19/0.39    inference(duplicate_literal_removal,[],[f143])).
% 0.19/0.39  fof(f143,plain,(
% 0.19/0.39    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(k7_relat_1(X0,X1),X2),k5_relat_1(X0,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X0) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | (~spl3_4 | ~spl3_7)),
% 0.19/0.39    inference(resolution,[],[f42,f54])).
% 0.19/0.39  fof(f54,plain,(
% 0.19/0.39    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) ) | ~spl3_7),
% 0.19/0.39    inference(avatar_component_clause,[],[f53])).
% 0.19/0.39  fof(f42,plain,(
% 0.19/0.39    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl3_4),
% 0.19/0.39    inference(avatar_component_clause,[],[f41])).
% 0.19/0.39  fof(f113,plain,(
% 0.19/0.39    spl3_17 | ~spl3_3 | ~spl3_6 | ~spl3_12),
% 0.19/0.39    inference(avatar_split_clause,[],[f109,f84,f49,f36,f111])).
% 0.19/0.39  fof(f49,plain,(
% 0.19/0.39    spl3_6 <=> ! [X1,X0] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.19/0.39    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.19/0.39  fof(f84,plain,(
% 0.19/0.39    spl3_12 <=> ! [X1] : k7_relat_1(sK1,X1) = k3_xboole_0(sK1,k7_relat_1(sK1,X1))),
% 0.19/0.39    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.19/0.39  fof(f109,plain,(
% 0.19/0.39    ( ! [X3] : (v1_relat_1(k7_relat_1(sK1,X3))) ) | (~spl3_3 | ~spl3_6 | ~spl3_12)),
% 0.19/0.39    inference(subsumption_resolution,[],[f108,f38])).
% 0.19/0.39  fof(f108,plain,(
% 0.19/0.39    ( ! [X3] : (v1_relat_1(k7_relat_1(sK1,X3)) | ~v1_relat_1(sK1)) ) | (~spl3_6 | ~spl3_12)),
% 0.19/0.39    inference(superposition,[],[f50,f85])).
% 0.19/0.39  fof(f85,plain,(
% 0.19/0.39    ( ! [X1] : (k7_relat_1(sK1,X1) = k3_xboole_0(sK1,k7_relat_1(sK1,X1))) ) | ~spl3_12),
% 0.19/0.39    inference(avatar_component_clause,[],[f84])).
% 0.19/0.39  fof(f50,plain,(
% 0.19/0.39    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl3_6),
% 0.19/0.39    inference(avatar_component_clause,[],[f49])).
% 0.19/0.39  fof(f86,plain,(
% 0.19/0.39    spl3_12 | ~spl3_3 | ~spl3_10),
% 0.19/0.39    inference(avatar_split_clause,[],[f76,f72,f36,f84])).
% 0.19/0.39  fof(f72,plain,(
% 0.19/0.39    spl3_10 <=> ! [X1,X0] : (k7_relat_1(X0,X1) = k3_xboole_0(X0,k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.19/0.39    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.19/0.39  fof(f76,plain,(
% 0.19/0.39    ( ! [X1] : (k7_relat_1(sK1,X1) = k3_xboole_0(sK1,k7_relat_1(sK1,X1))) ) | (~spl3_3 | ~spl3_10)),
% 0.19/0.39    inference(resolution,[],[f73,f38])).
% 0.19/0.39  fof(f73,plain,(
% 0.19/0.39    ( ! [X0,X1] : (~v1_relat_1(X0) | k7_relat_1(X0,X1) = k3_xboole_0(X0,k7_relat_1(X0,X1))) ) | ~spl3_10),
% 0.19/0.39    inference(avatar_component_clause,[],[f72])).
% 0.19/0.39  fof(f74,plain,(
% 0.19/0.39    spl3_10 | ~spl3_5 | ~spl3_7 | ~spl3_8),
% 0.19/0.39    inference(avatar_split_clause,[],[f70,f57,f53,f45,f72])).
% 0.19/0.39  fof(f45,plain,(
% 0.19/0.39    spl3_5 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.39    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.39  fof(f57,plain,(
% 0.19/0.39    spl3_8 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.19/0.39    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.19/0.39  fof(f70,plain,(
% 0.19/0.39    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k3_xboole_0(X0,k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | (~spl3_5 | ~spl3_7 | ~spl3_8)),
% 0.19/0.39    inference(forward_demodulation,[],[f69,f46])).
% 0.19/0.39  fof(f46,plain,(
% 0.19/0.39    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_5),
% 0.19/0.39    inference(avatar_component_clause,[],[f45])).
% 0.19/0.39  fof(f69,plain,(
% 0.19/0.39    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k3_xboole_0(k7_relat_1(X0,X1),X0) | ~v1_relat_1(X0)) ) | (~spl3_7 | ~spl3_8)),
% 0.19/0.39    inference(resolution,[],[f58,f54])).
% 0.19/0.39  fof(f58,plain,(
% 0.19/0.39    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl3_8),
% 0.19/0.39    inference(avatar_component_clause,[],[f57])).
% 0.19/0.39  fof(f59,plain,(
% 0.19/0.39    spl3_8),
% 0.19/0.39    inference(avatar_split_clause,[],[f24,f57])).
% 0.19/0.39  fof(f24,plain,(
% 0.19/0.39    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.19/0.39    inference(cnf_transformation,[],[f13])).
% 0.19/0.39  fof(f13,plain,(
% 0.19/0.39    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.19/0.39    inference(ennf_transformation,[],[f2])).
% 0.19/0.39  fof(f2,axiom,(
% 0.19/0.39    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.19/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.19/0.39  fof(f55,plain,(
% 0.19/0.39    spl3_7),
% 0.19/0.39    inference(avatar_split_clause,[],[f23,f53])).
% 0.19/0.39  fof(f23,plain,(
% 0.19/0.39    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.19/0.39    inference(cnf_transformation,[],[f12])).
% 0.19/0.39  fof(f12,plain,(
% 0.19/0.39    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.19/0.39    inference(ennf_transformation,[],[f5])).
% 0.19/0.39  fof(f5,axiom,(
% 0.19/0.39    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.19/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 0.19/0.39  fof(f51,plain,(
% 0.19/0.39    spl3_6),
% 0.19/0.39    inference(avatar_split_clause,[],[f22,f49])).
% 0.19/0.39  fof(f22,plain,(
% 0.19/0.39    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.19/0.39    inference(cnf_transformation,[],[f11])).
% 0.19/0.39  fof(f11,plain,(
% 0.19/0.39    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.19/0.39    inference(ennf_transformation,[],[f3])).
% 0.19/0.39  fof(f3,axiom,(
% 0.19/0.39    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.19/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 0.19/0.39  fof(f47,plain,(
% 0.19/0.39    spl3_5),
% 0.19/0.39    inference(avatar_split_clause,[],[f21,f45])).
% 0.19/0.39  fof(f21,plain,(
% 0.19/0.39    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.39    inference(cnf_transformation,[],[f1])).
% 0.19/0.39  fof(f1,axiom,(
% 0.19/0.39    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.39  fof(f43,plain,(
% 0.19/0.39    spl3_4),
% 0.19/0.39    inference(avatar_split_clause,[],[f20,f41])).
% 0.19/0.39  fof(f20,plain,(
% 0.19/0.39    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.39    inference(cnf_transformation,[],[f10])).
% 0.19/0.39  fof(f10,plain,(
% 0.19/0.39    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.39    inference(flattening,[],[f9])).
% 0.19/0.39  fof(f9,plain,(
% 0.19/0.39    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.39    inference(ennf_transformation,[],[f4])).
% 0.19/0.39  fof(f4,axiom,(
% 0.19/0.39    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))))))),
% 0.19/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relat_1)).
% 0.19/0.39  fof(f39,plain,(
% 0.19/0.39    spl3_3),
% 0.19/0.39    inference(avatar_split_clause,[],[f17,f36])).
% 0.19/0.39  fof(f17,plain,(
% 0.19/0.39    v1_relat_1(sK1)),
% 0.19/0.39    inference(cnf_transformation,[],[f16])).
% 0.19/0.39  fof(f16,plain,(
% 0.19/0.39    (~r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),sK2),k5_relat_1(sK1,sK2)) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 0.19/0.39    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f15,f14])).
% 0.19/0.39  fof(f14,plain,(
% 0.19/0.39    ? [X0,X1] : (? [X2] : (~r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2)) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),X2),k5_relat_1(sK1,X2)) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.19/0.39    introduced(choice_axiom,[])).
% 0.19/0.39  fof(f15,plain,(
% 0.19/0.39    ? [X2] : (~r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),X2),k5_relat_1(sK1,X2)) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),sK2),k5_relat_1(sK1,sK2)) & v1_relat_1(sK2))),
% 0.19/0.39    introduced(choice_axiom,[])).
% 0.19/0.39  fof(f8,plain,(
% 0.19/0.39    ? [X0,X1] : (? [X2] : (~r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2)) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.19/0.39    inference(ennf_transformation,[],[f7])).
% 0.19/0.39  fof(f7,negated_conjecture,(
% 0.19/0.39    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2))))),
% 0.19/0.39    inference(negated_conjecture,[],[f6])).
% 0.19/0.39  fof(f6,conjecture,(
% 0.19/0.39    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2))))),
% 0.19/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_relat_1)).
% 0.19/0.39  fof(f34,plain,(
% 0.19/0.39    spl3_2),
% 0.19/0.39    inference(avatar_split_clause,[],[f18,f31])).
% 0.19/0.39  fof(f18,plain,(
% 0.19/0.39    v1_relat_1(sK2)),
% 0.19/0.39    inference(cnf_transformation,[],[f16])).
% 0.19/0.39  fof(f29,plain,(
% 0.19/0.39    ~spl3_1),
% 0.19/0.39    inference(avatar_split_clause,[],[f19,f26])).
% 0.19/0.39  fof(f19,plain,(
% 0.19/0.39    ~r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),sK2),k5_relat_1(sK1,sK2))),
% 0.19/0.39    inference(cnf_transformation,[],[f16])).
% 0.19/0.39  % SZS output end Proof for theBenchmark
% 0.19/0.39  % (30563)------------------------------
% 0.19/0.39  % (30563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.39  % (30563)Termination reason: Refutation
% 0.19/0.39  
% 0.19/0.39  % (30563)Memory used [KB]: 10618
% 0.19/0.39  % (30563)Time elapsed: 0.007 s
% 0.19/0.39  % (30563)------------------------------
% 0.19/0.39  % (30563)------------------------------
% 0.19/0.39  % (30557)Success in time 0.064 s
%------------------------------------------------------------------------------
