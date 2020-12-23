%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 (  88 expanded)
%              Number of leaves         :   15 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :  139 ( 265 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f124,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f50,f61,f83,f98,f122])).

fof(f122,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | spl3_4
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | spl3_4
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f120,f49])).

fof(f49,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl3_4
  <=> r1_tarski(k3_subset_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f120,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f114,f60])).

fof(f60,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl3_5
  <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f114,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,k3_subset_1(sK0,sK1)))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f39,f44,f97,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f97,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_9
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f44,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl3_3
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f98,plain,
    ( spl3_9
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f93,f80,f95])).

fof(f80,plain,
    ( spl3_7
  <=> k3_subset_1(sK0,sK1) = k6_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f93,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_7 ),
    inference(superposition,[],[f22,f82])).

fof(f82,plain,
    ( k3_subset_1(sK0,sK1) = k6_subset_1(sK0,sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f80])).

fof(f22,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f83,plain,
    ( spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f62,f32,f80])).

fof(f32,plain,
    ( spl3_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f62,plain,
    ( k3_subset_1(sK0,sK1) = k6_subset_1(sK0,sK1)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f34,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f34,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f61,plain,
    ( spl3_5
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f51,f32,f58])).

fof(f51,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f34,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f50,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f21,f47])).

fof(f21,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),sK1)
    & r1_tarski(k3_subset_1(sK0,sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f15,f14])).

fof(f14,plain,
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

fof(f15,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k3_subset_1(sK0,X2),sK1)
        & r1_tarski(k3_subset_1(sK0,sK1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(k3_subset_1(sK0,sK2),sK1)
      & r1_tarski(k3_subset_1(sK0,sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(k3_subset_1(X0,X1),X2)
             => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(k3_subset_1(X0,X1),X2)
           => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

fof(f45,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f20,f42])).

fof(f20,plain,(
    r1_tarski(k3_subset_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f19,f37])).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f18,f32])).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:45:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.42  % (3559)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.43  % (3559)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f124,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f35,f40,f45,f50,f61,f83,f98,f122])).
% 0.21/0.43  fof(f122,plain,(
% 0.21/0.43    ~spl3_2 | ~spl3_3 | spl3_4 | ~spl3_5 | ~spl3_9),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f121])).
% 0.21/0.43  fof(f121,plain,(
% 0.21/0.43    $false | (~spl3_2 | ~spl3_3 | spl3_4 | ~spl3_5 | ~spl3_9)),
% 0.21/0.43    inference(subsumption_resolution,[],[f120,f49])).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    ~r1_tarski(k3_subset_1(sK0,sK2),sK1) | spl3_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f47])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    spl3_4 <=> r1_tarski(k3_subset_1(sK0,sK2),sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.43  fof(f120,plain,(
% 0.21/0.43    r1_tarski(k3_subset_1(sK0,sK2),sK1) | (~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_9)),
% 0.21/0.43    inference(forward_demodulation,[],[f114,f60])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl3_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f58])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    spl3_5 <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.43  fof(f114,plain,(
% 0.21/0.43    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,k3_subset_1(sK0,sK1))) | (~spl3_2 | ~spl3_3 | ~spl3_9)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f39,f44,f97,f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(nnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 0.21/0.43  fof(f97,plain,(
% 0.21/0.43    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_9),
% 0.21/0.43    inference(avatar_component_clause,[],[f95])).
% 0.21/0.43  fof(f95,plain,(
% 0.21/0.43    spl3_9 <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    r1_tarski(k3_subset_1(sK0,sK1),sK2) | ~spl3_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f42])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    spl3_3 <=> r1_tarski(k3_subset_1(sK0,sK1),sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f37])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.43  fof(f98,plain,(
% 0.21/0.43    spl3_9 | ~spl3_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f93,f80,f95])).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    spl3_7 <=> k3_subset_1(sK0,sK1) = k6_subset_1(sK0,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.43  fof(f93,plain,(
% 0.21/0.43    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_7),
% 0.21/0.43    inference(superposition,[],[f22,f82])).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    k3_subset_1(sK0,sK1) = k6_subset_1(sK0,sK1) | ~spl3_7),
% 0.21/0.43    inference(avatar_component_clause,[],[f80])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 0.21/0.43  fof(f83,plain,(
% 0.21/0.43    spl3_7 | ~spl3_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f62,f32,f80])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    spl3_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    k3_subset_1(sK0,sK1) = k6_subset_1(sK0,sK1) | ~spl3_1),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f34,f30])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.43    inference(definition_unfolding,[],[f25,f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f32])).
% 0.21/0.43  fof(f61,plain,(
% 0.21/0.43    spl3_5 | ~spl3_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f51,f32,f58])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl3_1),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f34,f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    ~spl3_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f21,f47])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ~r1_tarski(k3_subset_1(sK0,sK2),sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    (~r1_tarski(k3_subset_1(sK0,sK2),sK1) & r1_tarski(k3_subset_1(sK0,sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f15,f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK0,X2),sK1) & r1_tarski(k3_subset_1(sK0,sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ? [X2] : (~r1_tarski(k3_subset_1(sK0,X2),sK1) & r1_tarski(k3_subset_1(sK0,sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (~r1_tarski(k3_subset_1(sK0,sK2),sK1) & r1_tarski(k3_subset_1(sK0,sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(flattening,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X2) => r1_tarski(k3_subset_1(X0,X2),X1))))),
% 0.21/0.43    inference(negated_conjecture,[],[f7])).
% 0.21/0.43  fof(f7,conjecture,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X2) => r1_tarski(k3_subset_1(X0,X2),X1))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    spl3_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f20,f42])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    r1_tarski(k3_subset_1(sK0,sK1),sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f16])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    spl3_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f19,f37])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f16])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    spl3_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f18,f32])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f16])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (3559)------------------------------
% 0.21/0.43  % (3559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (3559)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (3559)Memory used [KB]: 10618
% 0.21/0.43  % (3559)Time elapsed: 0.009 s
% 0.21/0.43  % (3559)------------------------------
% 0.21/0.43  % (3559)------------------------------
% 0.21/0.43  % (3543)Success in time 0.077 s
%------------------------------------------------------------------------------
