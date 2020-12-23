%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 239 expanded)
%              Number of leaves         :   21 (  79 expanded)
%              Depth                    :   18
%              Number of atoms          :  456 (1212 expanded)
%              Number of equality atoms :  234 ( 678 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f401,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f188,f220,f245,f246,f267,f285,f317,f351,f361,f400])).

fof(f400,plain,
    ( spl5_8
    | spl5_9
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f394,f359,f170,f166])).

fof(f166,plain,
    ( spl5_8
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f170,plain,
    ( spl5_9
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f359,plain,
    ( spl5_18
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK2))
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f394,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl5_18 ),
    inference(resolution,[],[f360,f50])).

fof(f50,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f27,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f27,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK3 != k5_mcart_1(sK0,sK1,sK2,sK4)
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK3 = X5
                | k3_mcart_1(X5,X6,X7) != sK4
                | ~ m1_subset_1(X7,sK2) )
            | ~ m1_subset_1(X6,sK1) )
        | ~ m1_subset_1(X5,sK0) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f14,f23])).

% (11772)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f23,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k5_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X5
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK3 != k5_mcart_1(sK0,sK1,sK2,sK4)
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK3 = X5
                  | k3_mcart_1(X5,X6,X7) != sK4
                  | ~ m1_subset_1(X7,sK2) )
              | ~ m1_subset_1(X6,sK1) )
          | ~ m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X5
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X5
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X5 ) ) ) )
         => ( k5_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X5 ) ) ) )
       => ( k5_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_mcart_1)).

fof(f360,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK2))
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f359])).

fof(f361,plain,
    ( spl5_10
    | spl5_18
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f357,f243,f359,f174])).

fof(f174,plain,
    ( spl5_10
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f243,plain,
    ( spl5_16
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
        | ~ m1_subset_1(k7_mcart_1(X0,X1,X2,sK4),sK2)
        | k1_xboole_0 = X0
        | k1_xboole_0 = X1
        | k1_xboole_0 = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f357,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK2))
        | k1_xboole_0 = X0
        | k1_xboole_0 = X1
        | k1_xboole_0 = sK2 )
    | ~ spl5_16 ),
    inference(duplicate_literal_removal,[],[f353])).

fof(f353,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK2))
        | k1_xboole_0 = X0
        | k1_xboole_0 = X1
        | k1_xboole_0 = sK2
        | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK2)) )
    | ~ spl5_16 ),
    inference(resolution,[],[f244,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f48,f37])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(f244,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k7_mcart_1(X0,X1,X2,sK4),sK2)
        | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
        | k1_xboole_0 = X0
        | k1_xboole_0 = X1
        | k1_xboole_0 = X2 )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f243])).

fof(f351,plain,
    ( spl5_8
    | spl5_9
    | spl5_10
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f350,f240,f174,f170,f166])).

fof(f240,plain,
    ( spl5_15
  <=> ! [X3] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f350,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl5_15 ),
    inference(trivial_inequality_removal,[],[f347])).

fof(f347,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl5_15 ),
    inference(superposition,[],[f54,f338])).

fof(f338,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl5_15 ),
    inference(resolution,[],[f333,f50])).

fof(f333,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))
        | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1) )
    | ~ spl5_15 ),
    inference(resolution,[],[f326,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f326,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))
        | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1)) )
    | ~ spl5_15 ),
    inference(resolution,[],[f323,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f323,plain,
    ( ! [X0,X1] : ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))
    | ~ spl5_15 ),
    inference(resolution,[],[f241,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f241,plain,
    ( ! [X3] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X3,sK1))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f240])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f40,f37])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f25])).

% (11758)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f317,plain,
    ( spl5_8
    | spl5_9
    | spl5_10
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f316,f237,f174,f170,f166])).

fof(f237,plain,
    ( spl5_14
  <=> ! [X4] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f316,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl5_14 ),
    inference(trivial_inequality_removal,[],[f313])).

fof(f313,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl5_14 ),
    inference(superposition,[],[f54,f304])).

fof(f304,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl5_14 ),
    inference(resolution,[],[f299,f50])).

fof(f299,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))
        | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1) )
    | ~ spl5_14 ),
    inference(resolution,[],[f292,f33])).

fof(f292,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))
        | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1)) )
    | ~ spl5_14 ),
    inference(resolution,[],[f286,f35])).

fof(f286,plain,
    ( ! [X0,X1] : ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))
    | ~ spl5_14 ),
    inference(resolution,[],[f238,f38])).

fof(f238,plain,
    ( ! [X4] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X4))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f237])).

fof(f285,plain,(
    ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | ~ spl5_10 ),
    inference(trivial_inequality_removal,[],[f283])).

fof(f283,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl5_10 ),
    inference(superposition,[],[f31,f176])).

fof(f176,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f174])).

fof(f31,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f24])).

fof(f267,plain,(
    ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | ~ spl5_8 ),
    inference(trivial_inequality_removal,[],[f265])).

fof(f265,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl5_8 ),
    inference(superposition,[],[f29,f168])).

fof(f168,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f166])).

fof(f29,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f24])).

fof(f246,plain,
    ( spl5_8
    | spl5_9
    | spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f222,f182,f178,f174,f170,f166])).

fof(f178,plain,
    ( spl5_11
  <=> m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f182,plain,
    ( spl5_12
  <=> sK3 = k1_mcart_1(k1_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f222,plain,
    ( sK3 != k1_mcart_1(k1_mcart_1(sK4))
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f32,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f45,f37])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f32,plain,(
    sK3 != k5_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f245,plain,
    ( spl5_14
    | spl5_15
    | spl5_12
    | spl5_16 ),
    inference(avatar_split_clause,[],[f235,f243,f182,f240,f237])).

fof(f235,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | sK3 = k1_mcart_1(k1_mcart_1(sK4))
      | ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X3,sK1))
      | ~ m1_subset_1(k7_mcart_1(X0,X1,X2,sK4),sK2)
      | ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X4)) ) ),
    inference(equality_resolution,[],[f233])).

fof(f233,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sK4 != X3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_mcart_1(k1_mcart_1(X3)) = sK3
      | ~ r2_hidden(k1_mcart_1(X3),k2_zfmisc_1(X4,sK1))
      | ~ m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2)
      | ~ r2_hidden(k1_mcart_1(X3),k2_zfmisc_1(sK0,X5)) ) ),
    inference(resolution,[],[f232,f38])).

fof(f232,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(X0)),sK0)
      | ~ m1_subset_1(k7_mcart_1(X1,X2,X3,X0),sK2)
      | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | sK3 = k1_mcart_1(k1_mcart_1(X0))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X4,sK1))
      | sK4 != X0 ) ),
    inference(resolution,[],[f231,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f231,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k1_mcart_1(k1_mcart_1(X3)),sK0)
      | sK4 != X3
      | ~ m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_mcart_1(k1_mcart_1(X3)) = sK3
      | ~ r2_hidden(k1_mcart_1(X3),k2_zfmisc_1(X4,sK1)) ) ),
    inference(duplicate_literal_removal,[],[f230])).

fof(f230,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k1_mcart_1(k1_mcart_1(X3)),sK0)
      | sK4 != X3
      | ~ m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_mcart_1(k1_mcart_1(X3)) = sK3
      | ~ r2_hidden(k1_mcart_1(X3),k2_zfmisc_1(X4,sK1))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f227,f58])).

fof(f227,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k5_mcart_1(X0,X1,X2,X3),sK0)
      | sK4 != X3
      | ~ m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k5_mcart_1(X0,X1,X2,X3) = sK3
      | ~ r2_hidden(k1_mcart_1(X3),k2_zfmisc_1(X4,sK1)) ) ),
    inference(resolution,[],[f201,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f201,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(X9)),sK1)
      | ~ m1_subset_1(k7_mcart_1(X6,X7,X8,X9),sK2)
      | sK4 != X9
      | ~ m1_subset_1(k5_mcart_1(X6,X7,X8,X9),sK0)
      | ~ m1_subset_1(X9,k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8))
      | k1_xboole_0 = X8
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6
      | sK3 = k5_mcart_1(X6,X7,X8,X9) ) ),
    inference(resolution,[],[f199,f34])).

fof(f199,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_mcart_1(k1_mcart_1(X3)),sK1)
      | k5_mcart_1(X0,X1,X2,X3) = sK3
      | ~ m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2)
      | sK4 != X3
      | ~ m1_subset_1(k5_mcart_1(X0,X1,X2,X3),sK0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f198])).

fof(f198,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_mcart_1(k1_mcart_1(X3)),sK1)
      | k5_mcart_1(X0,X1,X2,X3) = sK3
      | ~ m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2)
      | sK4 != X3
      | ~ m1_subset_1(k5_mcart_1(X0,X1,X2,X3),sK0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f192,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f46,f37])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f192,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k6_mcart_1(X0,X1,X2,X3),sK1)
      | k5_mcart_1(X0,X1,X2,X3) = sK3
      | ~ m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2)
      | sK4 != X3
      | ~ m1_subset_1(k5_mcart_1(X0,X1,X2,X3),sK0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f49,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f44,f36,f37])).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f49,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK3 = X5
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(definition_unfolding,[],[f28,f36])).

fof(f28,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X5
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f220,plain,(
    ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | ~ spl5_9 ),
    inference(trivial_inequality_removal,[],[f218])).

fof(f218,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl5_9 ),
    inference(superposition,[],[f30,f172])).

fof(f172,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f170])).

fof(f30,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f188,plain,(
    spl5_11 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | spl5_11 ),
    inference(resolution,[],[f180,f50])).

fof(f180,plain,
    ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:16:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (11749)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (11777)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (11769)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (11761)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (11756)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (11749)Refutation not found, incomplete strategy% (11749)------------------------------
% 0.20/0.52  % (11749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (11749)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (11749)Memory used [KB]: 1663
% 0.20/0.52  % (11749)Time elapsed: 0.098 s
% 0.20/0.52  % (11749)------------------------------
% 0.20/0.52  % (11749)------------------------------
% 0.20/0.53  % (11767)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (11755)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (11771)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (11752)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (11763)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (11754)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (11750)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (11751)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (11776)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (11765)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (11764)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.55  % (11768)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (11778)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (11761)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f401,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f188,f220,f245,f246,f267,f285,f317,f351,f361,f400])).
% 0.20/0.55  fof(f400,plain,(
% 0.20/0.55    spl5_8 | spl5_9 | ~spl5_18),
% 0.20/0.55    inference(avatar_split_clause,[],[f394,f359,f170,f166])).
% 0.20/0.55  fof(f166,plain,(
% 0.20/0.55    spl5_8 <=> k1_xboole_0 = sK0),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.55  fof(f170,plain,(
% 0.20/0.55    spl5_9 <=> k1_xboole_0 = sK1),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.55  fof(f359,plain,(
% 0.20/0.55    spl5_18 <=> ! [X1,X0] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK2)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.20/0.55  fof(f394,plain,(
% 0.20/0.55    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl5_18),
% 0.20/0.55    inference(resolution,[],[f360,f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.55    inference(definition_unfolding,[],[f27,f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.20/0.55    inference(cnf_transformation,[],[f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    sK3 != k5_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X5 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f14,f23])).
% 0.20/0.55  % (11772)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X5 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k5_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X5 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f14,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X5 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.20/0.55    inference(flattening,[],[f13])).
% 0.20/0.55  fof(f13,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3,X4] : (((k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X5 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.55    inference(negated_conjecture,[],[f11])).
% 0.20/0.55  fof(f11,conjecture,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_mcart_1)).
% 0.20/0.55  fof(f360,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK2)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl5_18),
% 0.20/0.55    inference(avatar_component_clause,[],[f359])).
% 0.20/0.55  fof(f361,plain,(
% 0.20/0.55    spl5_10 | spl5_18 | ~spl5_16),
% 0.20/0.55    inference(avatar_split_clause,[],[f357,f243,f359,f174])).
% 0.20/0.55  fof(f174,plain,(
% 0.20/0.55    spl5_10 <=> k1_xboole_0 = sK2),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.55  fof(f243,plain,(
% 0.20/0.55    spl5_16 <=> ! [X1,X0,X2] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | ~m1_subset_1(k7_mcart_1(X0,X1,X2,sK4),sK2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.55  fof(f357,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK2)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = sK2) ) | ~spl5_16),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f353])).
% 0.20/0.55  fof(f353,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK2)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK2))) ) | ~spl5_16),
% 0.20/0.55    inference(resolution,[],[f244,f59])).
% 0.20/0.55  fof(f59,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f48,f37])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).
% 0.20/0.55  fof(f244,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(k7_mcart_1(X0,X1,X2,sK4),sK2) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2) ) | ~spl5_16),
% 0.20/0.55    inference(avatar_component_clause,[],[f243])).
% 0.20/0.55  fof(f351,plain,(
% 0.20/0.55    spl5_8 | spl5_9 | spl5_10 | ~spl5_15),
% 0.20/0.55    inference(avatar_split_clause,[],[f350,f240,f174,f170,f166])).
% 0.20/0.55  fof(f240,plain,(
% 0.20/0.55    spl5_15 <=> ! [X3] : ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X3,sK1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.55  fof(f350,plain,(
% 0.20/0.55    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl5_15),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f347])).
% 0.20/0.55  fof(f347,plain,(
% 0.20/0.55    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl5_15),
% 0.20/0.55    inference(superposition,[],[f54,f338])).
% 0.20/0.55  fof(f338,plain,(
% 0.20/0.55    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl5_15),
% 0.20/0.55    inference(resolution,[],[f333,f50])).
% 0.20/0.55  fof(f333,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1)) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1)) ) | ~spl5_15),
% 0.20/0.55    inference(resolution,[],[f326,f33])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.55  fof(f326,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))) ) | ~spl5_15),
% 0.20/0.55    inference(resolution,[],[f323,f35])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.55    inference(flattening,[],[f17])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.55  fof(f323,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))) ) | ~spl5_15),
% 0.20/0.55    inference(resolution,[],[f241,f38])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f19])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.20/0.55  fof(f241,plain,(
% 0.20/0.55    ( ! [X3] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X3,sK1))) ) | ~spl5_15),
% 0.20/0.55    inference(avatar_component_clause,[],[f240])).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(definition_unfolding,[],[f40,f37])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.55    inference(flattening,[],[f25])).
% 0.20/0.55  % (11758)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | (k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.55    inference(nnf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).
% 0.20/0.55  fof(f317,plain,(
% 0.20/0.55    spl5_8 | spl5_9 | spl5_10 | ~spl5_14),
% 0.20/0.55    inference(avatar_split_clause,[],[f316,f237,f174,f170,f166])).
% 0.20/0.55  fof(f237,plain,(
% 0.20/0.55    spl5_14 <=> ! [X4] : ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X4))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.55  fof(f316,plain,(
% 0.20/0.55    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl5_14),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f313])).
% 0.20/0.55  fof(f313,plain,(
% 0.20/0.55    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl5_14),
% 0.20/0.55    inference(superposition,[],[f54,f304])).
% 0.20/0.55  fof(f304,plain,(
% 0.20/0.55    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl5_14),
% 0.20/0.55    inference(resolution,[],[f299,f50])).
% 0.20/0.55  fof(f299,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1)) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1)) ) | ~spl5_14),
% 0.20/0.55    inference(resolution,[],[f292,f33])).
% 0.20/0.55  fof(f292,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))) ) | ~spl5_14),
% 0.20/0.55    inference(resolution,[],[f286,f35])).
% 0.20/0.55  fof(f286,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))) ) | ~spl5_14),
% 0.20/0.55    inference(resolution,[],[f238,f38])).
% 0.20/0.55  fof(f238,plain,(
% 0.20/0.55    ( ! [X4] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X4))) ) | ~spl5_14),
% 0.20/0.55    inference(avatar_component_clause,[],[f237])).
% 0.20/0.55  fof(f285,plain,(
% 0.20/0.55    ~spl5_10),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f284])).
% 0.20/0.55  fof(f284,plain,(
% 0.20/0.55    $false | ~spl5_10),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f283])).
% 0.20/0.55  fof(f283,plain,(
% 0.20/0.55    k1_xboole_0 != k1_xboole_0 | ~spl5_10),
% 0.20/0.55    inference(superposition,[],[f31,f176])).
% 0.20/0.55  fof(f176,plain,(
% 0.20/0.55    k1_xboole_0 = sK2 | ~spl5_10),
% 0.20/0.55    inference(avatar_component_clause,[],[f174])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    k1_xboole_0 != sK2),
% 0.20/0.55    inference(cnf_transformation,[],[f24])).
% 0.20/0.55  fof(f267,plain,(
% 0.20/0.55    ~spl5_8),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f266])).
% 0.20/0.55  fof(f266,plain,(
% 0.20/0.55    $false | ~spl5_8),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f265])).
% 0.20/0.55  fof(f265,plain,(
% 0.20/0.55    k1_xboole_0 != k1_xboole_0 | ~spl5_8),
% 0.20/0.55    inference(superposition,[],[f29,f168])).
% 0.20/0.55  fof(f168,plain,(
% 0.20/0.55    k1_xboole_0 = sK0 | ~spl5_8),
% 0.20/0.55    inference(avatar_component_clause,[],[f166])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    k1_xboole_0 != sK0),
% 0.20/0.55    inference(cnf_transformation,[],[f24])).
% 0.20/0.55  fof(f246,plain,(
% 0.20/0.55    spl5_8 | spl5_9 | spl5_10 | ~spl5_11 | ~spl5_12),
% 0.20/0.55    inference(avatar_split_clause,[],[f222,f182,f178,f174,f170,f166])).
% 0.20/0.55  fof(f178,plain,(
% 0.20/0.55    spl5_11 <=> m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.55  fof(f182,plain,(
% 0.20/0.55    spl5_12 <=> sK3 = k1_mcart_1(k1_mcart_1(sK4))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.55  fof(f222,plain,(
% 0.20/0.55    sK3 != k1_mcart_1(k1_mcart_1(sK4)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.55    inference(superposition,[],[f32,f58])).
% 0.20/0.55  fof(f58,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(definition_unfolding,[],[f45,f37])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.55    inference(ennf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    sK3 != k5_mcart_1(sK0,sK1,sK2,sK4)),
% 0.20/0.55    inference(cnf_transformation,[],[f24])).
% 0.20/0.55  fof(f245,plain,(
% 0.20/0.55    spl5_14 | spl5_15 | spl5_12 | spl5_16),
% 0.20/0.55    inference(avatar_split_clause,[],[f235,f243,f182,f240,f237])).
% 0.20/0.55  fof(f235,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | sK3 = k1_mcart_1(k1_mcart_1(sK4)) | ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X3,sK1)) | ~m1_subset_1(k7_mcart_1(X0,X1,X2,sK4),sK2) | ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X4))) )),
% 0.20/0.55    inference(equality_resolution,[],[f233])).
% 0.20/0.55  fof(f233,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (sK4 != X3 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_mcart_1(k1_mcart_1(X3)) = sK3 | ~r2_hidden(k1_mcart_1(X3),k2_zfmisc_1(X4,sK1)) | ~m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2) | ~r2_hidden(k1_mcart_1(X3),k2_zfmisc_1(sK0,X5))) )),
% 0.20/0.55    inference(resolution,[],[f232,f38])).
% 0.20/0.55  fof(f232,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(k1_mcart_1(k1_mcart_1(X0)),sK0) | ~m1_subset_1(k7_mcart_1(X1,X2,X3,X0),sK2) | ~m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | sK3 = k1_mcart_1(k1_mcart_1(X0)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X4,sK1)) | sK4 != X0) )),
% 0.20/0.55    inference(resolution,[],[f231,f34])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.55  fof(f231,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k1_mcart_1(k1_mcart_1(X3)),sK0) | sK4 != X3 | ~m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_mcart_1(k1_mcart_1(X3)) = sK3 | ~r2_hidden(k1_mcart_1(X3),k2_zfmisc_1(X4,sK1))) )),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f230])).
% 0.20/0.55  fof(f230,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k1_mcart_1(k1_mcart_1(X3)),sK0) | sK4 != X3 | ~m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_mcart_1(k1_mcart_1(X3)) = sK3 | ~r2_hidden(k1_mcart_1(X3),k2_zfmisc_1(X4,sK1)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(superposition,[],[f227,f58])).
% 0.20/0.55  fof(f227,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k5_mcart_1(X0,X1,X2,X3),sK0) | sK4 != X3 | ~m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k5_mcart_1(X0,X1,X2,X3) = sK3 | ~r2_hidden(k1_mcart_1(X3),k2_zfmisc_1(X4,sK1))) )),
% 0.20/0.55    inference(resolution,[],[f201,f39])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f19])).
% 0.20/0.55  fof(f201,plain,(
% 0.20/0.55    ( ! [X6,X8,X7,X9] : (~r2_hidden(k2_mcart_1(k1_mcart_1(X9)),sK1) | ~m1_subset_1(k7_mcart_1(X6,X7,X8,X9),sK2) | sK4 != X9 | ~m1_subset_1(k5_mcart_1(X6,X7,X8,X9),sK0) | ~m1_subset_1(X9,k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8)) | k1_xboole_0 = X8 | k1_xboole_0 = X7 | k1_xboole_0 = X6 | sK3 = k5_mcart_1(X6,X7,X8,X9)) )),
% 0.20/0.55    inference(resolution,[],[f199,f34])).
% 0.20/0.55  fof(f199,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k2_mcart_1(k1_mcart_1(X3)),sK1) | k5_mcart_1(X0,X1,X2,X3) = sK3 | ~m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2) | sK4 != X3 | ~m1_subset_1(k5_mcart_1(X0,X1,X2,X3),sK0) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f198])).
% 0.20/0.55  fof(f198,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k2_mcart_1(k1_mcart_1(X3)),sK1) | k5_mcart_1(X0,X1,X2,X3) = sK3 | ~m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2) | sK4 != X3 | ~m1_subset_1(k5_mcart_1(X0,X1,X2,X3),sK0) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(superposition,[],[f192,f57])).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(definition_unfolding,[],[f46,f37])).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f192,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k6_mcart_1(X0,X1,X2,X3),sK1) | k5_mcart_1(X0,X1,X2,X3) = sK3 | ~m1_subset_1(k7_mcart_1(X0,X1,X2,X3),sK2) | sK4 != X3 | ~m1_subset_1(k5_mcart_1(X0,X1,X2,X3),sK0) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(superposition,[],[f49,f55])).
% 0.20/0.55  fof(f55,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(definition_unfolding,[],[f44,f36,f37])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f20])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.55    inference(ennf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | sK3 = X5 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f28,f36])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ( ! [X6,X7,X5] : (sK3 = X5 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f24])).
% 0.20/0.55  fof(f220,plain,(
% 0.20/0.55    ~spl5_9),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f219])).
% 0.20/0.55  fof(f219,plain,(
% 0.20/0.55    $false | ~spl5_9),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f218])).
% 0.20/0.55  fof(f218,plain,(
% 0.20/0.55    k1_xboole_0 != k1_xboole_0 | ~spl5_9),
% 0.20/0.55    inference(superposition,[],[f30,f172])).
% 0.20/0.55  fof(f172,plain,(
% 0.20/0.55    k1_xboole_0 = sK1 | ~spl5_9),
% 0.20/0.55    inference(avatar_component_clause,[],[f170])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    k1_xboole_0 != sK1),
% 0.20/0.55    inference(cnf_transformation,[],[f24])).
% 0.20/0.55  fof(f188,plain,(
% 0.20/0.55    spl5_11),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f186])).
% 0.20/0.55  fof(f186,plain,(
% 0.20/0.55    $false | spl5_11),
% 0.20/0.55    inference(resolution,[],[f180,f50])).
% 0.20/0.55  fof(f180,plain,(
% 0.20/0.55    ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | spl5_11),
% 0.20/0.55    inference(avatar_component_clause,[],[f178])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (11761)------------------------------
% 0.20/0.55  % (11761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (11761)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (11761)Memory used [KB]: 6396
% 0.20/0.55  % (11759)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (11761)Time elapsed: 0.135 s
% 0.20/0.55  % (11761)------------------------------
% 0.20/0.55  % (11761)------------------------------
% 0.20/0.55  % (11770)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (11744)Success in time 0.192 s
%------------------------------------------------------------------------------
