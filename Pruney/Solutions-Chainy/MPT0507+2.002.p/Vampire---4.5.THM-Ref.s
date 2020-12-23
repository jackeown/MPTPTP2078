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
% DateTime   : Thu Dec  3 12:48:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 114 expanded)
%              Number of leaves         :   17 (  52 expanded)
%              Depth                    :    7
%              Number of atoms          :  188 ( 363 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f94,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f30,f35,f40,f44,f48,f52,f59,f63,f74,f90,f93])).

fof(f93,plain,
    ( spl3_1
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | spl3_1
    | ~ spl3_13 ),
    inference(resolution,[],[f86,f24])).

fof(f24,plain,
    ( ~ r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl3_1
  <=> r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f86,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK1,X0),k7_relat_1(sK2,X0))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_13
  <=> ! [X0] : r1_tarski(k7_relat_1(sK1,X0),k7_relat_1(sK2,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f90,plain,
    ( spl3_13
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f89,f72,f61,f57,f42,f85])).

fof(f42,plain,
    ( spl3_5
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f57,plain,
    ( spl3_8
  <=> ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f61,plain,
    ( spl3_9
  <=> ! [X1] : k7_relat_1(sK1,X1) = k5_relat_1(k6_relat_1(X1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f72,plain,
    ( spl3_11
  <=> ! [X0] :
        ( r1_tarski(k5_relat_1(X0,sK1),k5_relat_1(X0,sK2))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f89,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK1,X0),k7_relat_1(sK2,X0))
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f88,f62])).

fof(f62,plain,
    ( ! [X1] : k7_relat_1(sK1,X1) = k5_relat_1(k6_relat_1(X1),sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f61])).

fof(f88,plain,
    ( ! [X0] : r1_tarski(k5_relat_1(k6_relat_1(X0),sK1),k7_relat_1(sK2,X0))
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f77,f43])).

fof(f43,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f77,plain,
    ( ! [X0] :
        ( r1_tarski(k5_relat_1(k6_relat_1(X0),sK1),k7_relat_1(sK2,X0))
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(superposition,[],[f73,f58])).

fof(f58,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f73,plain,
    ( ! [X0] :
        ( r1_tarski(k5_relat_1(X0,sK1),k5_relat_1(X0,sK2))
        | ~ v1_relat_1(X0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f72])).

fof(f74,plain,
    ( spl3_11
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f70,f46,f37,f32,f27,f72])).

fof(f27,plain,
    ( spl3_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f32,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f37,plain,
    ( spl3_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f46,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f70,plain,
    ( ! [X0] :
        ( r1_tarski(k5_relat_1(X0,sK1),k5_relat_1(X0,sK2))
        | ~ v1_relat_1(X0) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f69,f39])).

fof(f39,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f69,plain,
    ( ! [X0] :
        ( r1_tarski(k5_relat_1(X0,sK1),k5_relat_1(X0,sK2))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK1) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f68,f34])).

fof(f34,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f68,plain,
    ( ! [X0] :
        ( r1_tarski(k5_relat_1(X0,sK1),k5_relat_1(X0,sK2))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(sK1) )
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(resolution,[],[f47,f29])).

fof(f29,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f47,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f46])).

fof(f63,plain,
    ( spl3_9
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f54,f50,f37,f61])).

fof(f50,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f54,plain,
    ( ! [X1] : k7_relat_1(sK1,X1) = k5_relat_1(k6_relat_1(X1),sK1)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(resolution,[],[f51,f39])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f50])).

fof(f59,plain,
    ( spl3_8
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f53,f50,f32,f57])).

fof(f53,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(resolution,[],[f51,f34])).

fof(f52,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f20,f50])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f48,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f19,f46])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

fof(f44,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f18,f42])).

fof(f18,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f40,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f14,f37])).

fof(f14,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
            & r1_tarski(X1,X2)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(X2,sK0))
          & r1_tarski(sK1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(X2,sK0))
        & r1_tarski(sK1,X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))
      & r1_tarski(sK1,sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          & r1_tarski(X1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          & r1_tarski(X1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

fof(f35,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f15,f32])).

fof(f15,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f16,f27])).

fof(f16,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f25,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f17,f22])).

fof(f17,plain,(
    ~ r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:50:08 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.44  % (27454)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.44  % (27457)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.44  % (27455)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.44  % (27454)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f94,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f25,f30,f35,f40,f44,f48,f52,f59,f63,f74,f90,f93])).
% 0.22/0.44  fof(f93,plain,(
% 0.22/0.44    spl3_1 | ~spl3_13),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f91])).
% 0.22/0.44  fof(f91,plain,(
% 0.22/0.44    $false | (spl3_1 | ~spl3_13)),
% 0.22/0.44    inference(resolution,[],[f86,f24])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ~r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)) | spl3_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f22])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    spl3_1 <=> r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.44  fof(f86,plain,(
% 0.22/0.44    ( ! [X0] : (r1_tarski(k7_relat_1(sK1,X0),k7_relat_1(sK2,X0))) ) | ~spl3_13),
% 0.22/0.44    inference(avatar_component_clause,[],[f85])).
% 0.22/0.44  fof(f85,plain,(
% 0.22/0.44    spl3_13 <=> ! [X0] : r1_tarski(k7_relat_1(sK1,X0),k7_relat_1(sK2,X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.44  fof(f90,plain,(
% 0.22/0.44    spl3_13 | ~spl3_5 | ~spl3_8 | ~spl3_9 | ~spl3_11),
% 0.22/0.44    inference(avatar_split_clause,[],[f89,f72,f61,f57,f42,f85])).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    spl3_5 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.44  fof(f57,plain,(
% 0.22/0.44    spl3_8 <=> ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.44  fof(f61,plain,(
% 0.22/0.44    spl3_9 <=> ! [X1] : k7_relat_1(sK1,X1) = k5_relat_1(k6_relat_1(X1),sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.44  fof(f72,plain,(
% 0.22/0.44    spl3_11 <=> ! [X0] : (r1_tarski(k5_relat_1(X0,sK1),k5_relat_1(X0,sK2)) | ~v1_relat_1(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.44  fof(f89,plain,(
% 0.22/0.44    ( ! [X0] : (r1_tarski(k7_relat_1(sK1,X0),k7_relat_1(sK2,X0))) ) | (~spl3_5 | ~spl3_8 | ~spl3_9 | ~spl3_11)),
% 0.22/0.44    inference(forward_demodulation,[],[f88,f62])).
% 0.22/0.44  fof(f62,plain,(
% 0.22/0.44    ( ! [X1] : (k7_relat_1(sK1,X1) = k5_relat_1(k6_relat_1(X1),sK1)) ) | ~spl3_9),
% 0.22/0.44    inference(avatar_component_clause,[],[f61])).
% 0.22/0.44  fof(f88,plain,(
% 0.22/0.44    ( ! [X0] : (r1_tarski(k5_relat_1(k6_relat_1(X0),sK1),k7_relat_1(sK2,X0))) ) | (~spl3_5 | ~spl3_8 | ~spl3_11)),
% 0.22/0.44    inference(subsumption_resolution,[],[f77,f43])).
% 0.22/0.44  fof(f43,plain,(
% 0.22/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl3_5),
% 0.22/0.44    inference(avatar_component_clause,[],[f42])).
% 0.22/0.44  fof(f77,plain,(
% 0.22/0.44    ( ! [X0] : (r1_tarski(k5_relat_1(k6_relat_1(X0),sK1),k7_relat_1(sK2,X0)) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl3_8 | ~spl3_11)),
% 0.22/0.44    inference(superposition,[],[f73,f58])).
% 0.22/0.44  fof(f58,plain,(
% 0.22/0.44    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)) ) | ~spl3_8),
% 0.22/0.44    inference(avatar_component_clause,[],[f57])).
% 0.22/0.44  fof(f73,plain,(
% 0.22/0.44    ( ! [X0] : (r1_tarski(k5_relat_1(X0,sK1),k5_relat_1(X0,sK2)) | ~v1_relat_1(X0)) ) | ~spl3_11),
% 0.22/0.44    inference(avatar_component_clause,[],[f72])).
% 0.22/0.44  fof(f74,plain,(
% 0.22/0.44    spl3_11 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f70,f46,f37,f32,f27,f72])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    spl3_2 <=> r1_tarski(sK1,sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    spl3_3 <=> v1_relat_1(sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    spl3_4 <=> v1_relat_1(sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    spl3_6 <=> ! [X1,X0,X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.44  fof(f70,plain,(
% 0.22/0.44    ( ! [X0] : (r1_tarski(k5_relat_1(X0,sK1),k5_relat_1(X0,sK2)) | ~v1_relat_1(X0)) ) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_6)),
% 0.22/0.44    inference(subsumption_resolution,[],[f69,f39])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    v1_relat_1(sK1) | ~spl3_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f37])).
% 0.22/0.44  fof(f69,plain,(
% 0.22/0.44    ( ! [X0] : (r1_tarski(k5_relat_1(X0,sK1),k5_relat_1(X0,sK2)) | ~v1_relat_1(X0) | ~v1_relat_1(sK1)) ) | (~spl3_2 | ~spl3_3 | ~spl3_6)),
% 0.22/0.44    inference(subsumption_resolution,[],[f68,f34])).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    v1_relat_1(sK2) | ~spl3_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f32])).
% 0.22/0.44  fof(f68,plain,(
% 0.22/0.44    ( ! [X0] : (r1_tarski(k5_relat_1(X0,sK1),k5_relat_1(X0,sK2)) | ~v1_relat_1(X0) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1)) ) | (~spl3_2 | ~spl3_6)),
% 0.22/0.44    inference(resolution,[],[f47,f29])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    r1_tarski(sK1,sK2) | ~spl3_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f27])).
% 0.22/0.44  fof(f47,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl3_6),
% 0.22/0.44    inference(avatar_component_clause,[],[f46])).
% 0.22/0.44  fof(f63,plain,(
% 0.22/0.44    spl3_9 | ~spl3_4 | ~spl3_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f54,f50,f37,f61])).
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    spl3_7 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.44  fof(f54,plain,(
% 0.22/0.44    ( ! [X1] : (k7_relat_1(sK1,X1) = k5_relat_1(k6_relat_1(X1),sK1)) ) | (~spl3_4 | ~spl3_7)),
% 0.22/0.44    inference(resolution,[],[f51,f39])).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl3_7),
% 0.22/0.44    inference(avatar_component_clause,[],[f50])).
% 0.22/0.44  fof(f59,plain,(
% 0.22/0.44    spl3_8 | ~spl3_3 | ~spl3_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f53,f50,f32,f57])).
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)) ) | (~spl3_3 | ~spl3_7)),
% 0.22/0.44    inference(resolution,[],[f51,f34])).
% 0.22/0.44  fof(f52,plain,(
% 0.22/0.44    spl3_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f20,f50])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.22/0.44  fof(f48,plain,(
% 0.22/0.44    spl3_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f19,f46])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(flattening,[],[f8])).
% 0.22/0.44  fof(f8,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).
% 0.22/0.44  fof(f44,plain,(
% 0.22/0.44    spl3_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f18,f42])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    spl3_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f14,f37])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    v1_relat_1(sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    (~r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)) & r1_tarski(sK1,sK2) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12,f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ? [X0,X1] : (? [X2] : (~r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) & r1_tarski(X1,X2) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(X2,sK0)) & r1_tarski(sK1,X2) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ? [X2] : (~r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(X2,sK0)) & r1_tarski(sK1,X2) & v1_relat_1(X2)) => (~r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)) & r1_tarski(sK1,sK2) & v1_relat_1(sK2))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f7,plain,(
% 0.22/0.44    ? [X0,X1] : (? [X2] : (~r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) & r1_tarski(X1,X2) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.22/0.44    inference(flattening,[],[f6])).
% 0.22/0.44  fof(f6,plain,(
% 0.22/0.44    ? [X0,X1] : (? [X2] : ((~r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) & r1_tarski(X1,X2)) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 0.22/0.44    inference(negated_conjecture,[],[f4])).
% 0.23/0.44  fof(f4,conjecture,(
% 0.23/0.44    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 0.23/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).
% 0.23/0.44  fof(f35,plain,(
% 0.23/0.44    spl3_3),
% 0.23/0.44    inference(avatar_split_clause,[],[f15,f32])).
% 0.23/0.44  fof(f15,plain,(
% 0.23/0.44    v1_relat_1(sK2)),
% 0.23/0.44    inference(cnf_transformation,[],[f13])).
% 0.23/0.44  fof(f30,plain,(
% 0.23/0.44    spl3_2),
% 0.23/0.44    inference(avatar_split_clause,[],[f16,f27])).
% 0.23/0.44  fof(f16,plain,(
% 0.23/0.44    r1_tarski(sK1,sK2)),
% 0.23/0.44    inference(cnf_transformation,[],[f13])).
% 0.23/0.44  fof(f25,plain,(
% 0.23/0.44    ~spl3_1),
% 0.23/0.44    inference(avatar_split_clause,[],[f17,f22])).
% 0.23/0.44  fof(f17,plain,(
% 0.23/0.44    ~r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))),
% 0.23/0.44    inference(cnf_transformation,[],[f13])).
% 0.23/0.44  % SZS output end Proof for theBenchmark
% 0.23/0.44  % (27454)------------------------------
% 0.23/0.44  % (27454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.44  % (27454)Termination reason: Refutation
% 0.23/0.44  
% 0.23/0.44  % (27454)Memory used [KB]: 10618
% 0.23/0.44  % (27454)Time elapsed: 0.006 s
% 0.23/0.44  % (27454)------------------------------
% 0.23/0.44  % (27454)------------------------------
% 0.23/0.44  % (27453)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.23/0.44  % (27448)Success in time 0.071 s
%------------------------------------------------------------------------------
