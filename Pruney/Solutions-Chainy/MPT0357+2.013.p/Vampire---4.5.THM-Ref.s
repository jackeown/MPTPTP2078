%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:28 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   60 (  97 expanded)
%              Number of leaves         :   16 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :  173 ( 318 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f175,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f32,f37,f42,f46,f50,f54,f66,f108,f115,f174])).

fof(f174,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f172,f26])).

fof(f26,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl3_1
  <=> r1_tarski(k3_subset_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f172,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),sK1)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f169,f41])).

fof(f41,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f169,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | r1_tarski(k3_subset_1(sK0,sK2),sK1)
    | ~ spl3_2
    | ~ spl3_17 ),
    inference(resolution,[],[f107,f31])).

fof(f31,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl3_2
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_subset_1(sK0,X0),sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | r1_tarski(k3_subset_1(sK0,sK2),X0) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl3_17
  <=> ! [X0] :
        ( ~ r1_tarski(k3_subset_1(sK0,X0),sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | r1_tarski(k3_subset_1(sK0,sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f115,plain,
    ( ~ spl3_3
    | ~ spl3_5
    | spl3_13 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_5
    | spl3_13 ),
    inference(subsumption_resolution,[],[f113,f36])).

fof(f36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f113,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_5
    | spl3_13 ),
    inference(resolution,[],[f92,f45])).

fof(f45,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f92,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_13
  <=> m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f108,plain,
    ( ~ spl3_13
    | spl3_17
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f87,f63,f52,f106,f90])).

fof(f52,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X1,X2)
        | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f63,plain,
    ( spl3_9
  <=> sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_subset_1(sK0,X0),sK2)
        | r1_tarski(k3_subset_1(sK0,sK2),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) )
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(superposition,[],[f53,f65])).

fof(f65,plain,
    ( sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f53,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
        | r1_tarski(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f52])).

fof(f66,plain,
    ( spl3_9
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f59,f48,f34,f63])).

fof(f48,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f59,plain,
    ( sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(resolution,[],[f49,f36])).

fof(f49,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f54,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f22,f52])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f50,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f20,f48])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f46,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f19,f44])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f42,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f15,f39])).

fof(f15,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),sK1)
    & r1_tarski(k3_subset_1(sK0,sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
            & r1_tarski(k3_subset_1(X0,X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK0,X2),sK1)
          & r1_tarski(k3_subset_1(sK0,sK1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k3_subset_1(sK0,X2),sK1)
        & r1_tarski(k3_subset_1(sK0,sK1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(k3_subset_1(sK0,sK2),sK1)
      & r1_tarski(k3_subset_1(sK0,sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(k3_subset_1(X0,X1),X2)
             => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(k3_subset_1(X0,X1),X2)
           => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

fof(f37,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f16,f34])).

fof(f16,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f32,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f17,f29])).

fof(f17,plain,(
    r1_tarski(k3_subset_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f27,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f18,f24])).

fof(f18,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:34:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.41  % (10221)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.19/0.41  % (10228)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.19/0.41  % (10229)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.19/0.42  % (10229)Refutation found. Thanks to Tanya!
% 0.19/0.42  % SZS status Theorem for theBenchmark
% 0.19/0.42  % SZS output start Proof for theBenchmark
% 0.19/0.42  fof(f175,plain,(
% 0.19/0.42    $false),
% 0.19/0.42    inference(avatar_sat_refutation,[],[f27,f32,f37,f42,f46,f50,f54,f66,f108,f115,f174])).
% 0.19/0.42  fof(f174,plain,(
% 0.19/0.42    spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_17),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f173])).
% 0.19/0.42  fof(f173,plain,(
% 0.19/0.42    $false | (spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_17)),
% 0.19/0.42    inference(subsumption_resolution,[],[f172,f26])).
% 0.19/0.42  fof(f26,plain,(
% 0.19/0.42    ~r1_tarski(k3_subset_1(sK0,sK2),sK1) | spl3_1),
% 0.19/0.42    inference(avatar_component_clause,[],[f24])).
% 0.19/0.42  fof(f24,plain,(
% 0.19/0.42    spl3_1 <=> r1_tarski(k3_subset_1(sK0,sK2),sK1)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.42  fof(f172,plain,(
% 0.19/0.42    r1_tarski(k3_subset_1(sK0,sK2),sK1) | (~spl3_2 | ~spl3_4 | ~spl3_17)),
% 0.19/0.42    inference(subsumption_resolution,[],[f169,f41])).
% 0.19/0.42  fof(f41,plain,(
% 0.19/0.42    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_4),
% 0.19/0.42    inference(avatar_component_clause,[],[f39])).
% 0.19/0.42  fof(f39,plain,(
% 0.19/0.42    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.42  fof(f169,plain,(
% 0.19/0.42    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | r1_tarski(k3_subset_1(sK0,sK2),sK1) | (~spl3_2 | ~spl3_17)),
% 0.19/0.42    inference(resolution,[],[f107,f31])).
% 0.19/0.42  fof(f31,plain,(
% 0.19/0.42    r1_tarski(k3_subset_1(sK0,sK1),sK2) | ~spl3_2),
% 0.19/0.42    inference(avatar_component_clause,[],[f29])).
% 0.19/0.42  fof(f29,plain,(
% 0.19/0.42    spl3_2 <=> r1_tarski(k3_subset_1(sK0,sK1),sK2)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.42  fof(f107,plain,(
% 0.19/0.42    ( ! [X0] : (~r1_tarski(k3_subset_1(sK0,X0),sK2) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r1_tarski(k3_subset_1(sK0,sK2),X0)) ) | ~spl3_17),
% 0.19/0.42    inference(avatar_component_clause,[],[f106])).
% 0.19/0.42  fof(f106,plain,(
% 0.19/0.42    spl3_17 <=> ! [X0] : (~r1_tarski(k3_subset_1(sK0,X0),sK2) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r1_tarski(k3_subset_1(sK0,sK2),X0))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.19/0.42  fof(f115,plain,(
% 0.19/0.42    ~spl3_3 | ~spl3_5 | spl3_13),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f114])).
% 0.19/0.42  fof(f114,plain,(
% 0.19/0.42    $false | (~spl3_3 | ~spl3_5 | spl3_13)),
% 0.19/0.42    inference(subsumption_resolution,[],[f113,f36])).
% 0.19/0.42  fof(f36,plain,(
% 0.19/0.42    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.19/0.42    inference(avatar_component_clause,[],[f34])).
% 0.19/0.42  fof(f34,plain,(
% 0.19/0.42    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.42  fof(f113,plain,(
% 0.19/0.42    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | (~spl3_5 | spl3_13)),
% 0.19/0.42    inference(resolution,[],[f92,f45])).
% 0.19/0.42  fof(f45,plain,(
% 0.19/0.42    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_5),
% 0.19/0.42    inference(avatar_component_clause,[],[f44])).
% 0.19/0.42  fof(f44,plain,(
% 0.19/0.42    spl3_5 <=> ! [X1,X0] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.42  fof(f92,plain,(
% 0.19/0.42    ~m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | spl3_13),
% 0.19/0.42    inference(avatar_component_clause,[],[f90])).
% 0.19/0.42  fof(f90,plain,(
% 0.19/0.42    spl3_13 <=> m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.19/0.42  fof(f108,plain,(
% 0.19/0.42    ~spl3_13 | spl3_17 | ~spl3_7 | ~spl3_9),
% 0.19/0.42    inference(avatar_split_clause,[],[f87,f63,f52,f106,f90])).
% 0.19/0.42  fof(f52,plain,(
% 0.19/0.42    spl3_7 <=> ! [X1,X0,X2] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.19/0.42  fof(f63,plain,(
% 0.19/0.42    spl3_9 <=> sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.19/0.42  fof(f87,plain,(
% 0.19/0.42    ( ! [X0] : (~r1_tarski(k3_subset_1(sK0,X0),sK2) | r1_tarski(k3_subset_1(sK0,sK2),X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))) ) | (~spl3_7 | ~spl3_9)),
% 0.19/0.42    inference(superposition,[],[f53,f65])).
% 0.19/0.42  fof(f65,plain,(
% 0.19/0.42    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) | ~spl3_9),
% 0.19/0.42    inference(avatar_component_clause,[],[f63])).
% 0.19/0.42  fof(f53,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_7),
% 0.19/0.42    inference(avatar_component_clause,[],[f52])).
% 0.19/0.42  fof(f66,plain,(
% 0.19/0.42    spl3_9 | ~spl3_3 | ~spl3_6),
% 0.19/0.42    inference(avatar_split_clause,[],[f59,f48,f34,f63])).
% 0.19/0.42  fof(f48,plain,(
% 0.19/0.42    spl3_6 <=> ! [X1,X0] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.19/0.42  fof(f59,plain,(
% 0.19/0.42    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) | (~spl3_3 | ~spl3_6)),
% 0.19/0.42    inference(resolution,[],[f49,f36])).
% 0.19/0.42  fof(f49,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) ) | ~spl3_6),
% 0.19/0.42    inference(avatar_component_clause,[],[f48])).
% 0.19/0.42  fof(f54,plain,(
% 0.19/0.42    spl3_7),
% 0.19/0.42    inference(avatar_split_clause,[],[f22,f52])).
% 0.19/0.42  fof(f22,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f14])).
% 0.19/0.42  fof(f14,plain,(
% 0.19/0.42    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.42    inference(nnf_transformation,[],[f10])).
% 0.19/0.42  fof(f10,plain,(
% 0.19/0.42    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.42    inference(ennf_transformation,[],[f3])).
% 0.19/0.42  fof(f3,axiom,(
% 0.19/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 0.19/0.42  fof(f50,plain,(
% 0.19/0.42    spl3_6),
% 0.19/0.42    inference(avatar_split_clause,[],[f20,f48])).
% 0.19/0.42  fof(f20,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f9])).
% 0.19/0.42  fof(f9,plain,(
% 0.19/0.42    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.42    inference(ennf_transformation,[],[f2])).
% 0.19/0.42  fof(f2,axiom,(
% 0.19/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.19/0.42  fof(f46,plain,(
% 0.19/0.42    spl3_5),
% 0.19/0.42    inference(avatar_split_clause,[],[f19,f44])).
% 0.19/0.42  fof(f19,plain,(
% 0.19/0.42    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f8])).
% 0.19/0.42  fof(f8,plain,(
% 0.19/0.42    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.42    inference(ennf_transformation,[],[f1])).
% 0.19/0.42  fof(f1,axiom,(
% 0.19/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.19/0.42  fof(f42,plain,(
% 0.19/0.42    spl3_4),
% 0.19/0.42    inference(avatar_split_clause,[],[f15,f39])).
% 0.19/0.42  fof(f15,plain,(
% 0.19/0.42    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.42    inference(cnf_transformation,[],[f13])).
% 0.19/0.42  fof(f13,plain,(
% 0.19/0.42    (~r1_tarski(k3_subset_1(sK0,sK2),sK1) & r1_tarski(k3_subset_1(sK0,sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12,f11])).
% 0.19/0.42  fof(f11,plain,(
% 0.19/0.42    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK0,X2),sK1) & r1_tarski(k3_subset_1(sK0,sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f12,plain,(
% 0.19/0.42    ? [X2] : (~r1_tarski(k3_subset_1(sK0,X2),sK1) & r1_tarski(k3_subset_1(sK0,sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (~r1_tarski(k3_subset_1(sK0,sK2),sK1) & r1_tarski(k3_subset_1(sK0,sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f7,plain,(
% 0.19/0.42    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.42    inference(flattening,[],[f6])).
% 0.19/0.42  fof(f6,plain,(
% 0.19/0.42    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.42    inference(ennf_transformation,[],[f5])).
% 0.19/0.42  fof(f5,negated_conjecture,(
% 0.19/0.42    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X2) => r1_tarski(k3_subset_1(X0,X2),X1))))),
% 0.19/0.42    inference(negated_conjecture,[],[f4])).
% 0.19/0.42  fof(f4,conjecture,(
% 0.19/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X2) => r1_tarski(k3_subset_1(X0,X2),X1))))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).
% 0.19/0.42  fof(f37,plain,(
% 0.19/0.42    spl3_3),
% 0.19/0.42    inference(avatar_split_clause,[],[f16,f34])).
% 0.19/0.42  fof(f16,plain,(
% 0.19/0.42    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.19/0.42    inference(cnf_transformation,[],[f13])).
% 0.19/0.42  fof(f32,plain,(
% 0.19/0.42    spl3_2),
% 0.19/0.42    inference(avatar_split_clause,[],[f17,f29])).
% 0.19/0.42  fof(f17,plain,(
% 0.19/0.42    r1_tarski(k3_subset_1(sK0,sK1),sK2)),
% 0.19/0.42    inference(cnf_transformation,[],[f13])).
% 0.19/0.42  fof(f27,plain,(
% 0.19/0.42    ~spl3_1),
% 0.19/0.42    inference(avatar_split_clause,[],[f18,f24])).
% 0.19/0.42  fof(f18,plain,(
% 0.19/0.42    ~r1_tarski(k3_subset_1(sK0,sK2),sK1)),
% 0.19/0.42    inference(cnf_transformation,[],[f13])).
% 0.19/0.42  % SZS output end Proof for theBenchmark
% 0.19/0.42  % (10229)------------------------------
% 0.19/0.42  % (10229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (10229)Termination reason: Refutation
% 0.19/0.42  
% 0.19/0.42  % (10229)Memory used [KB]: 6140
% 0.19/0.42  % (10229)Time elapsed: 0.007 s
% 0.19/0.42  % (10225)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.19/0.42  % (10229)------------------------------
% 0.19/0.42  % (10229)------------------------------
% 0.19/0.42  % (10218)Success in time 0.068 s
%------------------------------------------------------------------------------
