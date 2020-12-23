%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 105 expanded)
%              Number of leaves         :   23 (  50 expanded)
%              Depth                    :    6
%              Number of atoms          :  195 ( 268 expanded)
%              Number of equality atoms :   36 (  53 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f132,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f39,f43,f47,f51,f55,f59,f63,f76,f83,f105,f116,f123,f131])).

fof(f131,plain,
    ( ~ spl2_11
    | ~ spl2_16
    | ~ spl2_19 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | ~ spl2_11
    | ~ spl2_16
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f129,f75])).

fof(f75,plain,
    ( ! [X0] : k1_xboole_0 != k1_tarski(X0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl2_11
  <=> ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f129,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl2_16
    | ~ spl2_19 ),
    inference(resolution,[],[f122,f104])).

fof(f104,plain,
    ( r1_tarski(k1_tarski(sK0),k1_xboole_0)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl2_16
  <=> r1_tarski(k1_tarski(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl2_19
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f123,plain,
    ( spl2_19
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f119,f114,f45,f37,f121])).

fof(f37,plain,
    ( spl2_2
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f45,plain,
    ( spl2_4
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f114,plain,
    ( spl2_18
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k2_xboole_0(X0,X1)
        | ~ r1_tarski(X1,k1_xboole_0)
        | ~ r1_tarski(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f119,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_xboole_0) )
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f117,f46])).

fof(f46,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f117,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k2_xboole_0(X0,k1_xboole_0)
        | ~ r1_tarski(X0,k1_xboole_0) )
    | ~ spl2_2
    | ~ spl2_18 ),
    inference(resolution,[],[f115,f38])).

fof(f38,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f115,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,k1_xboole_0)
        | k1_xboole_0 = k2_xboole_0(X0,X1)
        | ~ r1_tarski(X0,k1_xboole_0) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f114])).

fof(f116,plain,
    ( spl2_18
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f112,f61,f37,f114])).

fof(f61,plain,
    ( spl2_8
  <=> ! [X1,X0,X2] :
        ( k2_xboole_0(X0,X2) = X1
        | ~ r1_tarski(X1,sK1(X0,X1,X2))
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k2_xboole_0(X0,X1)
        | ~ r1_tarski(X1,k1_xboole_0)
        | ~ r1_tarski(X0,k1_xboole_0) )
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(resolution,[],[f62,f38])).

fof(f62,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X1,sK1(X0,X1,X2))
        | k2_xboole_0(X0,X2) = X1
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f61])).

fof(f105,plain,
    ( spl2_16
    | ~ spl2_5
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f91,f80,f49,f102])).

fof(f49,plain,
    ( spl2_5
  <=> ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f80,plain,
    ( spl2_12
  <=> k1_xboole_0 = k1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f91,plain,
    ( r1_tarski(k1_tarski(sK0),k1_xboole_0)
    | ~ spl2_5
    | ~ spl2_12 ),
    inference(superposition,[],[f50,f82])).

fof(f82,plain,
    ( k1_xboole_0 = k1_zfmisc_1(sK0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f80])).

fof(f50,plain,
    ( ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f83,plain,
    ( spl2_12
    | spl2_1
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f78,f57,f41,f32,f80])).

fof(f32,plain,
    ( spl2_1
  <=> m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f41,plain,
    ( spl2_3
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f57,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f78,plain,
    ( k1_xboole_0 = k1_zfmisc_1(sK0)
    | spl2_1
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f77,f42])).

fof(f42,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f77,plain,
    ( k1_xboole_0 = k1_zfmisc_1(sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | spl2_1
    | ~ spl2_7 ),
    inference(resolution,[],[f58,f34])).

fof(f34,plain,
    ( ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f57])).

fof(f76,plain,
    ( spl2_11
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f72,f53,f45,f74])).

fof(f53,plain,
    ( spl2_6
  <=> ! [X1,X0] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f72,plain,
    ( ! [X0] : k1_xboole_0 != k1_tarski(X0)
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(superposition,[],[f54,f46])).

fof(f54,plain,
    ( ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f63,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f30,f61])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X2) = X1
      | ~ r1_tarski(X1,sK1(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ( ~ r1_tarski(X1,sK1(X0,X1,X2))
        & r1_tarski(X2,sK1(X0,X1,X2))
        & r1_tarski(X0,sK1(X0,X1,X2)) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
     => ( ~ r1_tarski(X1,sK1(X0,X1,X2))
        & r1_tarski(X2,sK1(X0,X1,X2))
        & r1_tarski(X0,sK1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X2,X3)
              & r1_tarski(X0,X3) )
           => r1_tarski(X1,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => k2_xboole_0(X0,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

fof(f59,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f27,f57])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

fof(f55,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f26,f53])).

fof(f26,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f51,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f25,f49])).

fof(f25,plain,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).

fof(f47,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f24,f45])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f43,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f23,f41])).

fof(f23,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f39,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f22,f37])).

fof(f22,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f35,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f21,f32])).

fof(f21,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f17])).

fof(f17,plain,
    ( ? [X0] : ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))
   => ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] : ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:04:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.40  % (22943)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.41  % (22942)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (22946)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.42  % (22946)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f132,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f35,f39,f43,f47,f51,f55,f59,f63,f76,f83,f105,f116,f123,f131])).
% 0.21/0.42  fof(f131,plain,(
% 0.21/0.42    ~spl2_11 | ~spl2_16 | ~spl2_19),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f130])).
% 0.21/0.42  fof(f130,plain,(
% 0.21/0.42    $false | (~spl2_11 | ~spl2_16 | ~spl2_19)),
% 0.21/0.42    inference(subsumption_resolution,[],[f129,f75])).
% 0.21/0.42  fof(f75,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) ) | ~spl2_11),
% 0.21/0.42    inference(avatar_component_clause,[],[f74])).
% 0.21/0.42  fof(f74,plain,(
% 0.21/0.42    spl2_11 <=> ! [X0] : k1_xboole_0 != k1_tarski(X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.42  fof(f129,plain,(
% 0.21/0.42    k1_xboole_0 = k1_tarski(sK0) | (~spl2_16 | ~spl2_19)),
% 0.21/0.42    inference(resolution,[],[f122,f104])).
% 0.21/0.42  fof(f104,plain,(
% 0.21/0.42    r1_tarski(k1_tarski(sK0),k1_xboole_0) | ~spl2_16),
% 0.21/0.42    inference(avatar_component_clause,[],[f102])).
% 0.21/0.42  fof(f102,plain,(
% 0.21/0.42    spl2_16 <=> r1_tarski(k1_tarski(sK0),k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.42  fof(f122,plain,(
% 0.21/0.42    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl2_19),
% 0.21/0.42    inference(avatar_component_clause,[],[f121])).
% 0.21/0.42  fof(f121,plain,(
% 0.21/0.42    spl2_19 <=> ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.42  fof(f123,plain,(
% 0.21/0.42    spl2_19 | ~spl2_2 | ~spl2_4 | ~spl2_18),
% 0.21/0.42    inference(avatar_split_clause,[],[f119,f114,f45,f37,f121])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    spl2_2 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    spl2_4 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.42  fof(f114,plain,(
% 0.21/0.42    spl2_18 <=> ! [X1,X0] : (k1_xboole_0 = k2_xboole_0(X0,X1) | ~r1_tarski(X1,k1_xboole_0) | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.42  fof(f119,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) ) | (~spl2_2 | ~spl2_4 | ~spl2_18)),
% 0.21/0.42    inference(forward_demodulation,[],[f117,f46])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f45])).
% 0.21/0.42  fof(f117,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = k2_xboole_0(X0,k1_xboole_0) | ~r1_tarski(X0,k1_xboole_0)) ) | (~spl2_2 | ~spl2_18)),
% 0.21/0.42    inference(resolution,[],[f115,f38])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl2_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f37])).
% 0.21/0.42  fof(f115,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = k2_xboole_0(X0,X1) | ~r1_tarski(X0,k1_xboole_0)) ) | ~spl2_18),
% 0.21/0.42    inference(avatar_component_clause,[],[f114])).
% 0.21/0.42  fof(f116,plain,(
% 0.21/0.42    spl2_18 | ~spl2_2 | ~spl2_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f112,f61,f37,f114])).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    spl2_8 <=> ! [X1,X0,X2] : (k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X1,sK1(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.42  fof(f112,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k1_xboole_0 = k2_xboole_0(X0,X1) | ~r1_tarski(X1,k1_xboole_0) | ~r1_tarski(X0,k1_xboole_0)) ) | (~spl2_2 | ~spl2_8)),
% 0.21/0.42    inference(resolution,[],[f62,f38])).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X1,sK1(X0,X1,X2)) | k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) ) | ~spl2_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f61])).
% 0.21/0.42  fof(f105,plain,(
% 0.21/0.42    spl2_16 | ~spl2_5 | ~spl2_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f91,f80,f49,f102])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    spl2_5 <=> ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.42  fof(f80,plain,(
% 0.21/0.42    spl2_12 <=> k1_xboole_0 = k1_zfmisc_1(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.42  fof(f91,plain,(
% 0.21/0.42    r1_tarski(k1_tarski(sK0),k1_xboole_0) | (~spl2_5 | ~spl2_12)),
% 0.21/0.42    inference(superposition,[],[f50,f82])).
% 0.21/0.42  fof(f82,plain,(
% 0.21/0.42    k1_xboole_0 = k1_zfmisc_1(sK0) | ~spl2_12),
% 0.21/0.42    inference(avatar_component_clause,[],[f80])).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))) ) | ~spl2_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f49])).
% 0.21/0.42  fof(f83,plain,(
% 0.21/0.42    spl2_12 | spl2_1 | ~spl2_3 | ~spl2_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f78,f57,f41,f32,f80])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    spl2_1 <=> m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    spl2_3 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.42  fof(f57,plain,(
% 0.21/0.42    spl2_7 <=> ! [X1,X0] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.42  fof(f78,plain,(
% 0.21/0.42    k1_xboole_0 = k1_zfmisc_1(sK0) | (spl2_1 | ~spl2_3 | ~spl2_7)),
% 0.21/0.42    inference(subsumption_resolution,[],[f77,f42])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl2_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f41])).
% 0.21/0.42  fof(f77,plain,(
% 0.21/0.42    k1_xboole_0 = k1_zfmisc_1(sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) | (spl2_1 | ~spl2_7)),
% 0.21/0.42    inference(resolution,[],[f58,f34])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl2_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f32])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) ) | ~spl2_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f57])).
% 0.21/0.42  fof(f76,plain,(
% 0.21/0.42    spl2_11 | ~spl2_4 | ~spl2_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f72,f53,f45,f74])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    spl2_6 <=> ! [X1,X0] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.42  fof(f72,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) ) | (~spl2_4 | ~spl2_6)),
% 0.21/0.42    inference(superposition,[],[f54,f46])).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) ) | ~spl2_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f53])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    spl2_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f30,f61])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X1,sK1(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (~r1_tarski(X1,sK1(X0,X1,X2)) & r1_tarski(X2,sK1(X0,X1,X2)) & r1_tarski(X0,sK1(X0,X1,X2))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) => (~r1_tarski(X1,sK1(X0,X1,X2)) & r1_tarski(X2,sK1(X0,X1,X2)) & r1_tarski(X0,sK1(X0,X1,X2))))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | ? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(flattening,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (? [X3] : (~r1_tarski(X1,X3) & (r1_tarski(X2,X3) & r1_tarski(X0,X3))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X3)) => r1_tarski(X1,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => k2_xboole_0(X0,X2) = X1)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    spl2_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f27,f57])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 0.21/0.42    inference(flattening,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0,X1] : ((m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X1,X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    spl2_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f26,f53])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    spl2_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f25,f49])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    spl2_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f24,f45])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    spl2_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f23,f41])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    spl2_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f22,f37])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    ~spl2_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f21,f32])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.42    inference(cnf_transformation,[],[f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ? [X0] : ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) => ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ? [X0] : ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,negated_conjecture,(
% 0.21/0.42    ~! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(negated_conjecture,[],[f9])).
% 0.21/0.42  fof(f9,conjecture,(
% 0.21/0.42    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (22946)------------------------------
% 0.21/0.42  % (22946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (22946)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (22946)Memory used [KB]: 6140
% 0.21/0.42  % (22946)Time elapsed: 0.006 s
% 0.21/0.42  % (22946)------------------------------
% 0.21/0.42  % (22946)------------------------------
% 0.21/0.42  % (22945)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.43  % (22935)Success in time 0.074 s
%------------------------------------------------------------------------------
