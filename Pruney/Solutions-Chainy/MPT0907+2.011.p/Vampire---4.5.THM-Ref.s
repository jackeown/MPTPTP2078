%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 107 expanded)
%              Number of leaves         :   19 (  46 expanded)
%              Depth                    :    6
%              Number of atoms          :  190 ( 290 expanded)
%              Number of equality atoms :   62 ( 101 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f107,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f38,f42,f46,f50,f61,f65,f69,f80,f85,f92,f104,f106])).

fof(f106,plain,
    ( ~ spl3_2
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f102,f99])).

fof(f99,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK2)
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f79,f33,f64])).

fof(f64,plain,
    ( ! [X2,X0,X1] :
        ( k1_mcart_1(X2) != X2
        | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( k1_mcart_1(X2) != X2
        | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f33,plain,
    ( sK0 = k1_mcart_1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl3_2
  <=> sK0 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f79,plain,
    ( m1_subset_1(sK0,k2_zfmisc_1(sK1,sK2))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_11
  <=> m1_subset_1(sK0,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f102,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK1,sK2)
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(superposition,[],[f45,f91])).

fof(f91,plain,
    ( k2_zfmisc_1(sK1,sK2) = k2_xboole_0(k1_tarski(sK0),k2_zfmisc_1(sK1,sK2))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_13
  <=> k2_zfmisc_1(sK1,sK2) = k2_xboole_0(k1_tarski(sK0),k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f45,plain,
    ( ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_5
  <=> ! [X1,X0] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f104,plain,
    ( ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f87,f102])).

fof(f87,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK2)
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(resolution,[],[f84,f79])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK0,k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK0,k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f92,plain,
    ( spl3_13
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f73,f59,f40,f26,f89])).

fof(f26,plain,
    ( spl3_1
  <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f40,plain,
    ( spl3_4
  <=> ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f59,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] :
        ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f73,plain,
    ( k2_zfmisc_1(sK1,sK2) = k2_xboole_0(k1_tarski(sK0),k2_zfmisc_1(sK1,sK2))
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f70,f41])).

fof(f41,plain,
    ( ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f70,plain,
    ( k2_zfmisc_1(sK1,sK2) = k2_xboole_0(k2_tarski(sK0,sK0),k2_zfmisc_1(sK1,sK2))
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f28,f28,f60])).

fof(f60,plain,
    ( ! [X2,X0,X1] :
        ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f59])).

fof(f28,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f85,plain,
    ( spl3_12
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f75,f67,f35,f83])).

fof(f35,plain,
    ( spl3_3
  <=> sK0 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f67,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( k2_mcart_1(X2) != X2
        | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK0,k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) )
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(trivial_inequality_removal,[],[f74])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( sK0 != sK0
        | ~ m1_subset_1(sK0,k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) )
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(superposition,[],[f68,f37])).

fof(f37,plain,
    ( sK0 = k2_mcart_1(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f68,plain,
    ( ! [X2,X0,X1] :
        ( k2_mcart_1(X2) != X2
        | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f80,plain,
    ( spl3_11
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f51,f48,f26,f77])).

fof(f48,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,X1)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f51,plain,
    ( m1_subset_1(sK0,k2_zfmisc_1(sK1,sK2))
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f28,f49])).

fof(f49,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | m1_subset_1(X0,X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f69,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f23,f67])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X2) != X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 )
          | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
     => ! [X2] :
          ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
         => ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_mcart_1)).

fof(f65,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f22,f63])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X2) != X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f61,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f24,f59])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).

fof(f50,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f21,f48])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f46,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f19,f44])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f42,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f18,f40])).

fof(f18,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,
    ( spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f17,f35,f31])).

fof(f17,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( sK0 = k2_mcart_1(sK0)
      | sK0 = k1_mcart_1(sK0) )
    & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
   => ( ( sK0 = k2_mcart_1(sK0)
        | sK0 = k1_mcart_1(sK0) )
      & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_mcart_1)).

fof(f29,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f16,f26])).

fof(f16,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:04:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.43  % (6568)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.44  % (6568)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f107,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f29,f38,f42,f46,f50,f61,f65,f69,f80,f85,f92,f104,f106])).
% 0.22/0.44  fof(f106,plain,(
% 0.22/0.44    ~spl3_2 | ~spl3_5 | ~spl3_9 | ~spl3_11 | ~spl3_13),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f105])).
% 0.22/0.44  fof(f105,plain,(
% 0.22/0.44    $false | (~spl3_2 | ~spl3_5 | ~spl3_9 | ~spl3_11 | ~spl3_13)),
% 0.22/0.44    inference(subsumption_resolution,[],[f102,f99])).
% 0.22/0.44  fof(f99,plain,(
% 0.22/0.44    k1_xboole_0 = k2_zfmisc_1(sK1,sK2) | (~spl3_2 | ~spl3_9 | ~spl3_11)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f79,f33,f64])).
% 0.22/0.44  fof(f64,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k1_mcart_1(X2) != X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) ) | ~spl3_9),
% 0.22/0.44    inference(avatar_component_clause,[],[f63])).
% 0.22/0.44  fof(f63,plain,(
% 0.22/0.44    spl3_9 <=> ! [X1,X0,X2] : (k1_mcart_1(X2) != X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = k2_zfmisc_1(X0,X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    sK0 = k1_mcart_1(sK0) | ~spl3_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f31])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    spl3_2 <=> sK0 = k1_mcart_1(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.44  fof(f79,plain,(
% 0.22/0.44    m1_subset_1(sK0,k2_zfmisc_1(sK1,sK2)) | ~spl3_11),
% 0.22/0.44    inference(avatar_component_clause,[],[f77])).
% 0.22/0.44  fof(f77,plain,(
% 0.22/0.44    spl3_11 <=> m1_subset_1(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.44  fof(f102,plain,(
% 0.22/0.44    k1_xboole_0 != k2_zfmisc_1(sK1,sK2) | (~spl3_5 | ~spl3_13)),
% 0.22/0.44    inference(superposition,[],[f45,f91])).
% 0.22/0.44  fof(f91,plain,(
% 0.22/0.44    k2_zfmisc_1(sK1,sK2) = k2_xboole_0(k1_tarski(sK0),k2_zfmisc_1(sK1,sK2)) | ~spl3_13),
% 0.22/0.44    inference(avatar_component_clause,[],[f89])).
% 0.22/0.44  fof(f89,plain,(
% 0.22/0.44    spl3_13 <=> k2_zfmisc_1(sK1,sK2) = k2_xboole_0(k1_tarski(sK0),k2_zfmisc_1(sK1,sK2))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.44  fof(f45,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) ) | ~spl3_5),
% 0.22/0.44    inference(avatar_component_clause,[],[f44])).
% 0.22/0.44  fof(f44,plain,(
% 0.22/0.44    spl3_5 <=> ! [X1,X0] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.44  fof(f104,plain,(
% 0.22/0.44    ~spl3_5 | ~spl3_11 | ~spl3_12 | ~spl3_13),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f103])).
% 0.22/0.44  fof(f103,plain,(
% 0.22/0.44    $false | (~spl3_5 | ~spl3_11 | ~spl3_12 | ~spl3_13)),
% 0.22/0.44    inference(subsumption_resolution,[],[f87,f102])).
% 0.22/0.44  fof(f87,plain,(
% 0.22/0.44    k1_xboole_0 = k2_zfmisc_1(sK1,sK2) | (~spl3_11 | ~spl3_12)),
% 0.22/0.44    inference(resolution,[],[f84,f79])).
% 0.22/0.44  fof(f84,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~m1_subset_1(sK0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) ) | ~spl3_12),
% 0.22/0.44    inference(avatar_component_clause,[],[f83])).
% 0.22/0.44  fof(f83,plain,(
% 0.22/0.44    spl3_12 <=> ! [X1,X0] : (~m1_subset_1(sK0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = k2_zfmisc_1(X0,X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.44  fof(f92,plain,(
% 0.22/0.44    spl3_13 | ~spl3_1 | ~spl3_4 | ~spl3_8),
% 0.22/0.44    inference(avatar_split_clause,[],[f73,f59,f40,f26,f89])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    spl3_1 <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    spl3_4 <=> ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.44  fof(f59,plain,(
% 0.22/0.44    spl3_8 <=> ! [X1,X0,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) = X1 | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.44  fof(f73,plain,(
% 0.22/0.44    k2_zfmisc_1(sK1,sK2) = k2_xboole_0(k1_tarski(sK0),k2_zfmisc_1(sK1,sK2)) | (~spl3_1 | ~spl3_4 | ~spl3_8)),
% 0.22/0.44    inference(forward_demodulation,[],[f70,f41])).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) ) | ~spl3_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f40])).
% 0.22/0.44  fof(f70,plain,(
% 0.22/0.44    k2_zfmisc_1(sK1,sK2) = k2_xboole_0(k2_tarski(sK0,sK0),k2_zfmisc_1(sK1,sK2)) | (~spl3_1 | ~spl3_8)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f28,f28,f60])).
% 0.22/0.44  fof(f60,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X0,X2),X1) = X1 | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) ) | ~spl3_8),
% 0.22/0.44    inference(avatar_component_clause,[],[f59])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) | ~spl3_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f26])).
% 0.22/0.44  fof(f85,plain,(
% 0.22/0.44    spl3_12 | ~spl3_3 | ~spl3_10),
% 0.22/0.44    inference(avatar_split_clause,[],[f75,f67,f35,f83])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    spl3_3 <=> sK0 = k2_mcart_1(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.44  fof(f67,plain,(
% 0.22/0.44    spl3_10 <=> ! [X1,X0,X2] : (k2_mcart_1(X2) != X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = k2_zfmisc_1(X0,X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.44  fof(f75,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~m1_subset_1(sK0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) ) | (~spl3_3 | ~spl3_10)),
% 0.22/0.44    inference(trivial_inequality_removal,[],[f74])).
% 0.22/0.44  fof(f74,plain,(
% 0.22/0.44    ( ! [X0,X1] : (sK0 != sK0 | ~m1_subset_1(sK0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) ) | (~spl3_3 | ~spl3_10)),
% 0.22/0.44    inference(superposition,[],[f68,f37])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    sK0 = k2_mcart_1(sK0) | ~spl3_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f35])).
% 0.22/0.44  fof(f68,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k2_mcart_1(X2) != X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) ) | ~spl3_10),
% 0.22/0.44    inference(avatar_component_clause,[],[f67])).
% 0.22/0.44  fof(f80,plain,(
% 0.22/0.44    spl3_11 | ~spl3_1 | ~spl3_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f51,f48,f26,f77])).
% 0.22/0.44  fof(f48,plain,(
% 0.22/0.44    spl3_6 <=> ! [X1,X0] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    m1_subset_1(sK0,k2_zfmisc_1(sK1,sK2)) | (~spl3_1 | ~spl3_6)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f28,f49])).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) ) | ~spl3_6),
% 0.22/0.44    inference(avatar_component_clause,[],[f48])).
% 0.22/0.44  fof(f69,plain,(
% 0.22/0.44    spl3_10),
% 0.22/0.44    inference(avatar_split_clause,[],[f23,f67])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k2_mcart_1(X2) != X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ! [X0,X1] : (! [X2] : ((k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2) | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1))) | k1_xboole_0 = k2_zfmisc_1(X0,X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) => ! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_mcart_1)).
% 0.22/0.44  fof(f65,plain,(
% 0.22/0.44    spl3_9),
% 0.22/0.44    inference(avatar_split_clause,[],[f22,f63])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k1_mcart_1(X2) != X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f61,plain,(
% 0.22/0.44    spl3_8),
% 0.22/0.44    inference(avatar_split_clause,[],[f24,f59])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X0,X2),X1) = X1 | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) = X1 | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.44    inference(flattening,[],[f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) = X1 | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    spl3_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f21,f48])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    spl3_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f19,f44])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    spl3_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f18,f40])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    spl3_2 | spl3_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f17,f35,f31])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    (sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ? [X0,X1,X2] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & r2_hidden(X0,k2_zfmisc_1(X1,X2))) => ((sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ? [X0,X1,X2] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.44    inference(ennf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.22/0.44    inference(negated_conjecture,[],[f7])).
% 0.22/0.44  fof(f7,conjecture,(
% 0.22/0.44    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_mcart_1)).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    spl3_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f16,f26])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.22/0.44    inference(cnf_transformation,[],[f15])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (6568)------------------------------
% 0.22/0.44  % (6568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (6568)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (6568)Memory used [KB]: 6140
% 0.22/0.44  % (6568)Time elapsed: 0.007 s
% 0.22/0.44  % (6568)------------------------------
% 0.22/0.44  % (6568)------------------------------
% 0.22/0.44  % (6562)Success in time 0.073 s
%------------------------------------------------------------------------------
