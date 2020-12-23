%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:22 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 118 expanded)
%              Number of leaves         :   17 (  50 expanded)
%              Depth                    :    7
%              Number of atoms          :  218 ( 453 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f95,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f38,f43,f48,f52,f56,f60,f67,f74,f84,f94])).

fof(f94,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f92,f32])).

fof(f32,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl3_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f92,plain,
    ( ~ r1_tarski(sK2,sK1)
    | spl3_1
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f91,f42])).

fof(f42,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f91,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(sK2,sK1)
    | spl3_1
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f90,f73])).

fof(f73,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl3_10
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f90,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(sK2,sK1)
    | spl3_1
    | ~ spl3_12 ),
    inference(resolution,[],[f83,f27])).

fof(f27,plain,
    ( ~ r1_tarski(sK2,k7_relat_1(sK1,sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl3_1
  <=> r1_tarski(sK2,k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f83,plain,
    ( ! [X2,X3] :
        ( r1_tarski(X2,k7_relat_1(sK1,X3))
        | ~ r1_tarski(k1_relat_1(X2),X3)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X2,sK1) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl3_12
  <=> ! [X3,X2] :
        ( ~ r1_tarski(X2,sK1)
        | ~ r1_tarski(k1_relat_1(X2),X3)
        | ~ v1_relat_1(X2)
        | r1_tarski(X2,k7_relat_1(sK1,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f84,plain,
    ( spl3_12
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f76,f54,f45,f82])).

fof(f45,plain,
    ( spl3_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f54,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X2,k7_relat_1(X1,X0))
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(k1_relat_1(X2),X0)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f76,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,sK1)
        | ~ r1_tarski(k1_relat_1(X2),X3)
        | ~ v1_relat_1(X2)
        | r1_tarski(X2,k7_relat_1(sK1,X3)) )
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(resolution,[],[f55,f47])).

fof(f47,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f55,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(k1_relat_1(X2),X0)
        | ~ v1_relat_1(X2)
        | r1_tarski(X2,k7_relat_1(X1,X0)) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f54])).

fof(f74,plain,
    ( spl3_10
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f69,f64,f50,f40,f71])).

fof(f50,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f64,plain,
    ( spl3_9
  <=> sK2 = k7_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f69,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f68,f42])).

fof(f68,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(superposition,[],[f51,f66])).

fof(f66,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f64])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f50])).

fof(f67,plain,
    ( spl3_9
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f62,f58,f40,f35,f64])).

fof(f35,plain,
    ( spl3_3
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f58,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = X1
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f62,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f61,f42])).

fof(f61,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(resolution,[],[f59,f37])).

fof(f37,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( ~ v4_relat_1(X1,X0)
        | k7_relat_1(X1,X0) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f58])).

fof(f60,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f23,f58])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f56,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f22,f54])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k7_relat_1(X1,X0))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k7_relat_1(X1,X0))
          | ~ r1_tarski(X2,X1)
          | ~ r1_tarski(k1_relat_1(X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k7_relat_1(X1,X0))
          | ~ r1_tarski(X2,X1)
          | ~ r1_tarski(k1_relat_1(X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( ( r1_tarski(X2,X1)
              & r1_tarski(k1_relat_1(X2),X0) )
           => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_relat_1)).

fof(f52,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f21,f50])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f48,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f16,f45])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_tarski(sK2,k7_relat_1(sK1,sK0))
    & r1_tarski(sK2,sK1)
    & v4_relat_1(sK2,sK0)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f14,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
            & r1_tarski(X2,X1)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(sK1,sK0))
          & r1_tarski(X2,sK1)
          & v4_relat_1(X2,sK0)
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X2] :
        ( ~ r1_tarski(X2,k7_relat_1(sK1,sK0))
        & r1_tarski(X2,sK1)
        & v4_relat_1(X2,sK0)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK2,k7_relat_1(sK1,sK0))
      & r1_tarski(sK2,sK1)
      & v4_relat_1(sK2,sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( ( v4_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => ( r1_tarski(X2,X1)
             => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => ( r1_tarski(X2,X1)
           => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t210_relat_1)).

fof(f43,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f17,f40])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f18,f35])).

fof(f18,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f19,f30])).

fof(f19,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f28,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f20,f25])).

fof(f20,plain,(
    ~ r1_tarski(sK2,k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:07:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.41  % (23618)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.14/0.41  % (23618)Refutation found. Thanks to Tanya!
% 0.14/0.41  % SZS status Theorem for theBenchmark
% 0.14/0.41  % SZS output start Proof for theBenchmark
% 0.14/0.41  fof(f95,plain,(
% 0.14/0.41    $false),
% 0.14/0.41    inference(avatar_sat_refutation,[],[f28,f33,f38,f43,f48,f52,f56,f60,f67,f74,f84,f94])).
% 0.14/0.41  fof(f94,plain,(
% 0.14/0.41    spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_10 | ~spl3_12),
% 0.14/0.41    inference(avatar_contradiction_clause,[],[f93])).
% 0.14/0.41  fof(f93,plain,(
% 0.14/0.41    $false | (spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_10 | ~spl3_12)),
% 0.14/0.41    inference(subsumption_resolution,[],[f92,f32])).
% 0.14/0.41  fof(f32,plain,(
% 0.14/0.41    r1_tarski(sK2,sK1) | ~spl3_2),
% 0.14/0.41    inference(avatar_component_clause,[],[f30])).
% 0.14/0.41  fof(f30,plain,(
% 0.14/0.41    spl3_2 <=> r1_tarski(sK2,sK1)),
% 0.14/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.14/0.41  fof(f92,plain,(
% 0.14/0.41    ~r1_tarski(sK2,sK1) | (spl3_1 | ~spl3_4 | ~spl3_10 | ~spl3_12)),
% 0.14/0.41    inference(subsumption_resolution,[],[f91,f42])).
% 0.22/0.41  fof(f42,plain,(
% 0.22/0.41    v1_relat_1(sK2) | ~spl3_4),
% 0.22/0.41    inference(avatar_component_clause,[],[f40])).
% 0.22/0.41  fof(f40,plain,(
% 0.22/0.41    spl3_4 <=> v1_relat_1(sK2)),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.41  fof(f91,plain,(
% 0.22/0.41    ~v1_relat_1(sK2) | ~r1_tarski(sK2,sK1) | (spl3_1 | ~spl3_10 | ~spl3_12)),
% 0.22/0.41    inference(subsumption_resolution,[],[f90,f73])).
% 0.22/0.41  fof(f73,plain,(
% 0.22/0.41    r1_tarski(k1_relat_1(sK2),sK0) | ~spl3_10),
% 0.22/0.41    inference(avatar_component_clause,[],[f71])).
% 0.22/0.41  fof(f71,plain,(
% 0.22/0.41    spl3_10 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.41  fof(f90,plain,(
% 0.22/0.41    ~r1_tarski(k1_relat_1(sK2),sK0) | ~v1_relat_1(sK2) | ~r1_tarski(sK2,sK1) | (spl3_1 | ~spl3_12)),
% 0.22/0.41    inference(resolution,[],[f83,f27])).
% 0.22/0.41  fof(f27,plain,(
% 0.22/0.41    ~r1_tarski(sK2,k7_relat_1(sK1,sK0)) | spl3_1),
% 0.22/0.41    inference(avatar_component_clause,[],[f25])).
% 0.22/0.41  fof(f25,plain,(
% 0.22/0.41    spl3_1 <=> r1_tarski(sK2,k7_relat_1(sK1,sK0))),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.41  fof(f83,plain,(
% 0.22/0.41    ( ! [X2,X3] : (r1_tarski(X2,k7_relat_1(sK1,X3)) | ~r1_tarski(k1_relat_1(X2),X3) | ~v1_relat_1(X2) | ~r1_tarski(X2,sK1)) ) | ~spl3_12),
% 0.22/0.41    inference(avatar_component_clause,[],[f82])).
% 0.22/0.41  fof(f82,plain,(
% 0.22/0.41    spl3_12 <=> ! [X3,X2] : (~r1_tarski(X2,sK1) | ~r1_tarski(k1_relat_1(X2),X3) | ~v1_relat_1(X2) | r1_tarski(X2,k7_relat_1(sK1,X3)))),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.41  fof(f84,plain,(
% 0.22/0.41    spl3_12 | ~spl3_5 | ~spl3_7),
% 0.22/0.41    inference(avatar_split_clause,[],[f76,f54,f45,f82])).
% 0.22/0.41  fof(f45,plain,(
% 0.22/0.41    spl3_5 <=> v1_relat_1(sK1)),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.41  fof(f54,plain,(
% 0.22/0.41    spl3_7 <=> ! [X1,X0,X2] : (r1_tarski(X2,k7_relat_1(X1,X0)) | ~r1_tarski(X2,X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.41  fof(f76,plain,(
% 0.22/0.41    ( ! [X2,X3] : (~r1_tarski(X2,sK1) | ~r1_tarski(k1_relat_1(X2),X3) | ~v1_relat_1(X2) | r1_tarski(X2,k7_relat_1(sK1,X3))) ) | (~spl3_5 | ~spl3_7)),
% 0.22/0.41    inference(resolution,[],[f55,f47])).
% 0.22/0.41  fof(f47,plain,(
% 0.22/0.41    v1_relat_1(sK1) | ~spl3_5),
% 0.22/0.41    inference(avatar_component_clause,[],[f45])).
% 0.22/0.41  fof(f55,plain,(
% 0.22/0.41    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X2,X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2) | r1_tarski(X2,k7_relat_1(X1,X0))) ) | ~spl3_7),
% 0.22/0.41    inference(avatar_component_clause,[],[f54])).
% 0.22/0.41  fof(f74,plain,(
% 0.22/0.41    spl3_10 | ~spl3_4 | ~spl3_6 | ~spl3_9),
% 0.22/0.41    inference(avatar_split_clause,[],[f69,f64,f50,f40,f71])).
% 0.22/0.41  fof(f50,plain,(
% 0.22/0.41    spl3_6 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.41  fof(f64,plain,(
% 0.22/0.41    spl3_9 <=> sK2 = k7_relat_1(sK2,sK0)),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.41  fof(f69,plain,(
% 0.22/0.41    r1_tarski(k1_relat_1(sK2),sK0) | (~spl3_4 | ~spl3_6 | ~spl3_9)),
% 0.22/0.41    inference(subsumption_resolution,[],[f68,f42])).
% 0.22/0.41  fof(f68,plain,(
% 0.22/0.41    r1_tarski(k1_relat_1(sK2),sK0) | ~v1_relat_1(sK2) | (~spl3_6 | ~spl3_9)),
% 0.22/0.41    inference(superposition,[],[f51,f66])).
% 0.22/0.41  fof(f66,plain,(
% 0.22/0.41    sK2 = k7_relat_1(sK2,sK0) | ~spl3_9),
% 0.22/0.41    inference(avatar_component_clause,[],[f64])).
% 0.22/0.41  fof(f51,plain,(
% 0.22/0.41    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) ) | ~spl3_6),
% 0.22/0.41    inference(avatar_component_clause,[],[f50])).
% 0.22/0.41  fof(f67,plain,(
% 0.22/0.41    spl3_9 | ~spl3_3 | ~spl3_4 | ~spl3_8),
% 0.22/0.41    inference(avatar_split_clause,[],[f62,f58,f40,f35,f64])).
% 0.22/0.41  fof(f35,plain,(
% 0.22/0.41    spl3_3 <=> v4_relat_1(sK2,sK0)),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.41  fof(f58,plain,(
% 0.22/0.41    spl3_8 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.41  fof(f62,plain,(
% 0.22/0.41    sK2 = k7_relat_1(sK2,sK0) | (~spl3_3 | ~spl3_4 | ~spl3_8)),
% 0.22/0.41    inference(subsumption_resolution,[],[f61,f42])).
% 0.22/0.41  fof(f61,plain,(
% 0.22/0.41    sK2 = k7_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | (~spl3_3 | ~spl3_8)),
% 0.22/0.41    inference(resolution,[],[f59,f37])).
% 0.22/0.41  fof(f37,plain,(
% 0.22/0.41    v4_relat_1(sK2,sK0) | ~spl3_3),
% 0.22/0.41    inference(avatar_component_clause,[],[f35])).
% 0.22/0.41  fof(f59,plain,(
% 0.22/0.41    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) ) | ~spl3_8),
% 0.22/0.41    inference(avatar_component_clause,[],[f58])).
% 0.22/0.41  fof(f60,plain,(
% 0.22/0.41    spl3_8),
% 0.22/0.41    inference(avatar_split_clause,[],[f23,f58])).
% 0.22/0.41  fof(f23,plain,(
% 0.22/0.41    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.41    inference(cnf_transformation,[],[f12])).
% 0.22/0.41  fof(f12,plain,(
% 0.22/0.41    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.41    inference(flattening,[],[f11])).
% 0.22/0.41  fof(f11,plain,(
% 0.22/0.41    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.41    inference(ennf_transformation,[],[f2])).
% 0.22/0.41  fof(f2,axiom,(
% 0.22/0.41    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.41  fof(f56,plain,(
% 0.22/0.41    spl3_7),
% 0.22/0.41    inference(avatar_split_clause,[],[f22,f54])).
% 0.22/0.41  fof(f22,plain,(
% 0.22/0.41    ( ! [X2,X0,X1] : (r1_tarski(X2,k7_relat_1(X1,X0)) | ~r1_tarski(X2,X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.41    inference(cnf_transformation,[],[f10])).
% 0.22/0.41  fof(f10,plain,(
% 0.22/0.41    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k7_relat_1(X1,X0)) | ~r1_tarski(X2,X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.41    inference(flattening,[],[f9])).
% 0.22/0.41  fof(f9,plain,(
% 0.22/0.41    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k7_relat_1(X1,X0)) | (~r1_tarski(X2,X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.41    inference(ennf_transformation,[],[f1])).
% 0.22/0.41  fof(f1,axiom,(
% 0.22/0.41    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ((r1_tarski(X2,X1) & r1_tarski(k1_relat_1(X2),X0)) => r1_tarski(X2,k7_relat_1(X1,X0)))))),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_relat_1)).
% 0.22/0.41  fof(f52,plain,(
% 0.22/0.41    spl3_6),
% 0.22/0.41    inference(avatar_split_clause,[],[f21,f50])).
% 0.22/0.41  fof(f21,plain,(
% 0.22/0.41    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.41    inference(cnf_transformation,[],[f8])).
% 0.22/0.41  fof(f8,plain,(
% 0.22/0.41    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.22/0.41    inference(ennf_transformation,[],[f3])).
% 0.22/0.41  fof(f3,axiom,(
% 0.22/0.41    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.22/0.41  fof(f48,plain,(
% 0.22/0.41    spl3_5),
% 0.22/0.41    inference(avatar_split_clause,[],[f16,f45])).
% 0.22/0.41  fof(f16,plain,(
% 0.22/0.41    v1_relat_1(sK1)),
% 0.22/0.41    inference(cnf_transformation,[],[f15])).
% 0.22/0.41  fof(f15,plain,(
% 0.22/0.41    (~r1_tarski(sK2,k7_relat_1(sK1,sK0)) & r1_tarski(sK2,sK1) & v4_relat_1(sK2,sK0) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 0.22/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f14,f13])).
% 0.22/0.41  fof(f13,plain,(
% 0.22/0.41    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k7_relat_1(X1,X0)) & r1_tarski(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(X2,k7_relat_1(sK1,sK0)) & r1_tarski(X2,sK1) & v4_relat_1(X2,sK0) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.22/0.41    introduced(choice_axiom,[])).
% 0.22/0.41  fof(f14,plain,(
% 0.22/0.41    ? [X2] : (~r1_tarski(X2,k7_relat_1(sK1,sK0)) & r1_tarski(X2,sK1) & v4_relat_1(X2,sK0) & v1_relat_1(X2)) => (~r1_tarski(sK2,k7_relat_1(sK1,sK0)) & r1_tarski(sK2,sK1) & v4_relat_1(sK2,sK0) & v1_relat_1(sK2))),
% 0.22/0.41    introduced(choice_axiom,[])).
% 0.22/0.41  fof(f7,plain,(
% 0.22/0.41    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k7_relat_1(X1,X0)) & r1_tarski(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.22/0.41    inference(flattening,[],[f6])).
% 0.22/0.41  fof(f6,plain,(
% 0.22/0.41    ? [X0,X1] : (? [X2] : ((~r1_tarski(X2,k7_relat_1(X1,X0)) & r1_tarski(X2,X1)) & (v4_relat_1(X2,X0) & v1_relat_1(X2))) & v1_relat_1(X1))),
% 0.22/0.41    inference(ennf_transformation,[],[f5])).
% 0.22/0.41  fof(f5,negated_conjecture,(
% 0.22/0.41    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => (r1_tarski(X2,X1) => r1_tarski(X2,k7_relat_1(X1,X0)))))),
% 0.22/0.41    inference(negated_conjecture,[],[f4])).
% 0.22/0.41  fof(f4,conjecture,(
% 0.22/0.41    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => (r1_tarski(X2,X1) => r1_tarski(X2,k7_relat_1(X1,X0)))))),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t210_relat_1)).
% 0.22/0.41  fof(f43,plain,(
% 0.22/0.41    spl3_4),
% 0.22/0.41    inference(avatar_split_clause,[],[f17,f40])).
% 0.22/0.41  fof(f17,plain,(
% 0.22/0.41    v1_relat_1(sK2)),
% 0.22/0.41    inference(cnf_transformation,[],[f15])).
% 0.22/0.41  fof(f38,plain,(
% 0.22/0.41    spl3_3),
% 0.22/0.41    inference(avatar_split_clause,[],[f18,f35])).
% 0.22/0.41  fof(f18,plain,(
% 0.22/0.41    v4_relat_1(sK2,sK0)),
% 0.22/0.41    inference(cnf_transformation,[],[f15])).
% 0.22/0.41  fof(f33,plain,(
% 0.22/0.41    spl3_2),
% 0.22/0.41    inference(avatar_split_clause,[],[f19,f30])).
% 0.22/0.41  fof(f19,plain,(
% 0.22/0.41    r1_tarski(sK2,sK1)),
% 0.22/0.41    inference(cnf_transformation,[],[f15])).
% 0.22/0.41  fof(f28,plain,(
% 0.22/0.41    ~spl3_1),
% 0.22/0.41    inference(avatar_split_clause,[],[f20,f25])).
% 0.22/0.41  fof(f20,plain,(
% 0.22/0.41    ~r1_tarski(sK2,k7_relat_1(sK1,sK0))),
% 0.22/0.41    inference(cnf_transformation,[],[f15])).
% 0.22/0.41  % SZS output end Proof for theBenchmark
% 0.22/0.41  % (23618)------------------------------
% 0.22/0.41  % (23618)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.41  % (23618)Termination reason: Refutation
% 0.22/0.41  
% 0.22/0.41  % (23618)Memory used [KB]: 10618
% 0.22/0.41  % (23618)Time elapsed: 0.004 s
% 0.22/0.41  % (23618)------------------------------
% 0.22/0.41  % (23618)------------------------------
% 0.22/0.41  % (23612)Success in time 0.051 s
%------------------------------------------------------------------------------
