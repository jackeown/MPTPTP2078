%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0906+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 (  97 expanded)
%              Number of leaves         :   13 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :  166 ( 295 expanded)
%              Number of equality atoms :   92 ( 176 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f93,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f32,f36,f50,f56,f67,f75,f84,f92])).

fof(f92,plain,
    ( spl3_5
    | spl3_6
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f89,f30,f23,f48,f45])).

fof(f45,plain,
    ( spl3_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f48,plain,
    ( spl3_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f23,plain,
    ( spl3_1
  <=> sK2 = k1_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f30,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f89,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(resolution,[],[f88,f31])).

fof(f31,plain,
    ( m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl3_1 ),
    inference(trivial_inequality_removal,[],[f87])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( sK2 != sK2
        | ~ m1_subset_1(sK2,k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl3_1 ),
    inference(superposition,[],[f18,f24])).

fof(f24,plain,
    ( sK2 = k1_mcart_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X2) != X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 )
          | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => ( k2_mcart_1(X2) != X2
                & k1_mcart_1(X2) != X2 ) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).

fof(f84,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | spl3_9 ),
    inference(trivial_inequality_removal,[],[f82])).

fof(f82,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl3_9 ),
    inference(superposition,[],[f66,f20])).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f66,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl3_9
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f75,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | spl3_7 ),
    inference(trivial_inequality_removal,[],[f73])).

fof(f73,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl3_7 ),
    inference(superposition,[],[f55,f21])).

fof(f21,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_7
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f67,plain,
    ( ~ spl3_9
    | spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f62,f48,f34,f65])).

fof(f34,plain,
    ( spl3_4
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f62,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl3_4
    | ~ spl3_6 ),
    inference(superposition,[],[f35,f49])).

fof(f49,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f35,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f34])).

fof(f56,plain,
    ( ~ spl3_7
    | spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f51,f45,f34,f54])).

fof(f51,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl3_4
    | ~ spl3_5 ),
    inference(superposition,[],[f35,f46])).

fof(f46,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f50,plain,
    ( spl3_5
    | spl3_6
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f41,f30,f26,f48,f45])).

fof(f26,plain,
    ( spl3_2
  <=> sK2 = k2_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f41,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(resolution,[],[f40,f31])).

fof(f40,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl3_2 ),
    inference(trivial_inequality_removal,[],[f39])).

fof(f39,plain,
    ( ! [X0,X1] :
        ( sK2 != sK2
        | ~ m1_subset_1(sK2,k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl3_2 ),
    inference(superposition,[],[f19,f27])).

fof(f27,plain,
    ( sK2 = k2_mcart_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X2) != X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f36,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f12,f34])).

fof(f12,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ( sK2 = k2_mcart_1(sK2)
      | sK2 = k1_mcart_1(sK2) )
    & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f8,f7])).

fof(f7,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( k2_mcart_1(X2) = X2
              | k1_mcart_1(X2) = X2 )
            & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
        & k2_zfmisc_1(X0,X1) != k1_xboole_0 )
   => ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1)) )
      & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,
    ( ? [X2] :
        ( ( k2_mcart_1(X2) = X2
          | k1_mcart_1(X2) = X2 )
        & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1)) )
   => ( ( sK2 = k2_mcart_1(sK2)
        | sK2 = k1_mcart_1(sK2) )
      & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      & k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k1_xboole_0
       => ! [X2] :
            ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
           => ( k2_mcart_1(X2) != X2
              & k1_mcart_1(X2) != X2 ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
     => ! [X2] :
          ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
         => ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_mcart_1)).

fof(f32,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f13,f30])).

fof(f13,plain,(
    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f28,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f14,f26,f23])).

fof(f14,plain,
    ( sK2 = k2_mcart_1(sK2)
    | sK2 = k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
