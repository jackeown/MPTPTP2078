%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 163 expanded)
%              Number of leaves         :   27 (  71 expanded)
%              Depth                    :    9
%              Number of atoms          :  294 ( 542 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f183,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f51,f60,f62,f66,f70,f74,f86,f90,f107,f120,f124,f128,f155,f159,f162,f178,f182])).

fof(f182,plain,
    ( ~ spl3_3
    | ~ spl3_17
    | ~ spl3_20
    | spl3_22 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_17
    | ~ spl3_20
    | spl3_22 ),
    inference(subsumption_resolution,[],[f154,f179])).

fof(f179,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl3_3
    | ~ spl3_17
    | spl3_22 ),
    inference(unit_resulting_resolution,[],[f55,f177,f127])).

fof(f127,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl3_17
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f177,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | spl3_22 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl3_22
  <=> r1_tarski(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f55,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl3_3
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f154,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl3_20
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f178,plain,
    ( ~ spl3_22
    | ~ spl3_2
    | spl3_4
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f164,f122,f57,f48,f175])).

fof(f48,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f57,plain,
    ( spl3_4
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f122,plain,
    ( spl3_16
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f164,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_2
    | spl3_4
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f58,f130])).

fof(f130,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_16 ),
    inference(unit_resulting_resolution,[],[f50,f123])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f122])).

fof(f50,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f58,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f162,plain,
    ( ~ spl3_2
    | ~ spl3_4
    | ~ spl3_16
    | ~ spl3_21 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_16
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f50,f160])).

fof(f160,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_4
    | ~ spl3_16
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f131,f158])).

fof(f158,plain,
    ( ! [X0] : ~ r1_tarski(sK1,k4_xboole_0(X0,sK2))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl3_21
  <=> ! [X0] : ~ r1_tarski(sK1,k4_xboole_0(X0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f131,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(superposition,[],[f59,f123])).

fof(f59,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f159,plain,
    ( spl3_21
    | spl3_3
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f114,f105,f72,f53,f157])).

fof(f72,plain,
    ( spl3_7
  <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f105,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

% (8271)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
fof(f114,plain,
    ( ! [X0] : ~ r1_tarski(sK1,k4_xboole_0(X0,sK2))
    | spl3_3
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f54,f73,f106])).

fof(f106,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f105])).

fof(f73,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f54,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f155,plain,
    ( spl3_20
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f135,f117,f84,f68,f152])).

fof(f68,plain,
    ( spl3_6
  <=> ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f84,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( r1_tarski(X0,k3_tarski(X1))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f117,plain,
    ( spl3_15
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f135,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f133,f69])).

fof(f69,plain,
    ( ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f133,plain,
    ( r1_tarski(sK1,k3_tarski(k1_zfmisc_1(sK0)))
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f119,f85])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k3_tarski(X1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f84])).

fof(f119,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f117])).

fof(f128,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f41,f126])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f124,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f39,f122])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f120,plain,
    ( spl3_15
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f108,f88,f64,f43,f117])).

fof(f43,plain,
    ( spl3_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f64,plain,
    ( spl3_5
  <=> ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f88,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( r2_hidden(X1,X0)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f108,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f65,f45,f89])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,X0)
        | r2_hidden(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f88])).

fof(f45,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f65,plain,
    ( ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f107,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f40,f105])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f90,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f34,f88])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f86,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f38,f84])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f74,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f32,f72])).

fof(f32,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f70,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f31,f68])).

fof(f31,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f66,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f30,f64])).

fof(f30,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f62,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f61,f57,f53])).

fof(f61,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f29,f59])).

fof(f29,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
      | ~ r1_xboole_0(sK1,sK2) )
    & ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
      | r1_xboole_0(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f23,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | r1_xboole_0(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,X2))
            | ~ r1_xboole_0(sK1,X2) )
          & ( r1_tarski(sK1,k3_subset_1(sK0,X2))
            | r1_xboole_0(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,X2))
          | ~ r1_xboole_0(sK1,X2) )
        & ( r1_tarski(sK1,k3_subset_1(sK0,X2))
          | r1_xboole_0(sK1,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
        | ~ r1_xboole_0(sK1,sK2) )
      & ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
        | r1_xboole_0(sK1,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
            | ~ r1_xboole_0(X1,X2) )
          & ( r1_tarski(X1,k3_subset_1(X0,X2))
            | r1_xboole_0(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
            | ~ r1_xboole_0(X1,X2) )
          & ( r1_tarski(X1,k3_subset_1(X0,X2))
            | r1_xboole_0(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,X2)
          <~> r1_tarski(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,X2)
            <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

fof(f60,plain,
    ( spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f28,f57,f53])).

fof(f28,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f27,f48])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f46,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f26,f43])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:26:04 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (8261)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (8261)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f183,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f46,f51,f60,f62,f66,f70,f74,f86,f90,f107,f120,f124,f128,f155,f159,f162,f178,f182])).
% 0.22/0.48  fof(f182,plain,(
% 0.22/0.48    ~spl3_3 | ~spl3_17 | ~spl3_20 | spl3_22),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f181])).
% 0.22/0.48  fof(f181,plain,(
% 0.22/0.48    $false | (~spl3_3 | ~spl3_17 | ~spl3_20 | spl3_22)),
% 0.22/0.48    inference(subsumption_resolution,[],[f154,f179])).
% 0.22/0.48  fof(f179,plain,(
% 0.22/0.48    ~r1_tarski(sK1,sK0) | (~spl3_3 | ~spl3_17 | spl3_22)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f55,f177,f127])).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl3_17),
% 0.22/0.48    inference(avatar_component_clause,[],[f126])).
% 0.22/0.48  fof(f126,plain,(
% 0.22/0.48    spl3_17 <=> ! [X1,X0,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.48  fof(f177,plain,(
% 0.22/0.48    ~r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | spl3_22),
% 0.22/0.48    inference(avatar_component_clause,[],[f175])).
% 0.22/0.48  fof(f175,plain,(
% 0.22/0.48    spl3_22 <=> r1_tarski(sK1,k4_xboole_0(sK0,sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    r1_xboole_0(sK1,sK2) | ~spl3_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f53])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    spl3_3 <=> r1_xboole_0(sK1,sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.48  fof(f154,plain,(
% 0.22/0.48    r1_tarski(sK1,sK0) | ~spl3_20),
% 0.22/0.48    inference(avatar_component_clause,[],[f152])).
% 0.22/0.48  fof(f152,plain,(
% 0.22/0.48    spl3_20 <=> r1_tarski(sK1,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.48  fof(f178,plain,(
% 0.22/0.48    ~spl3_22 | ~spl3_2 | spl3_4 | ~spl3_16),
% 0.22/0.48    inference(avatar_split_clause,[],[f164,f122,f57,f48,f175])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    spl3_4 <=> r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    spl3_16 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.48  fof(f164,plain,(
% 0.22/0.48    ~r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | (~spl3_2 | spl3_4 | ~spl3_16)),
% 0.22/0.48    inference(forward_demodulation,[],[f58,f130])).
% 0.22/0.48  fof(f130,plain,(
% 0.22/0.48    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | (~spl3_2 | ~spl3_16)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f50,f123])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_16),
% 0.22/0.48    inference(avatar_component_clause,[],[f122])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f48])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    ~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | spl3_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f57])).
% 0.22/0.48  fof(f162,plain,(
% 0.22/0.48    ~spl3_2 | ~spl3_4 | ~spl3_16 | ~spl3_21),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f161])).
% 0.22/0.48  fof(f161,plain,(
% 0.22/0.48    $false | (~spl3_2 | ~spl3_4 | ~spl3_16 | ~spl3_21)),
% 0.22/0.48    inference(subsumption_resolution,[],[f50,f160])).
% 0.22/0.48  fof(f160,plain,(
% 0.22/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | (~spl3_4 | ~spl3_16 | ~spl3_21)),
% 0.22/0.48    inference(subsumption_resolution,[],[f131,f158])).
% 0.22/0.48  fof(f158,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_tarski(sK1,k4_xboole_0(X0,sK2))) ) | ~spl3_21),
% 0.22/0.48    inference(avatar_component_clause,[],[f157])).
% 0.22/0.48  fof(f157,plain,(
% 0.22/0.48    spl3_21 <=> ! [X0] : ~r1_tarski(sK1,k4_xboole_0(X0,sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | (~spl3_4 | ~spl3_16)),
% 0.22/0.48    inference(superposition,[],[f59,f123])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~spl3_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f57])).
% 0.22/0.48  fof(f159,plain,(
% 0.22/0.48    spl3_21 | spl3_3 | ~spl3_7 | ~spl3_14),
% 0.22/0.48    inference(avatar_split_clause,[],[f114,f105,f72,f53,f157])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    spl3_7 <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.48  fof(f105,plain,(
% 0.22/0.48    spl3_14 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.48  % (8271)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  fof(f114,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_tarski(sK1,k4_xboole_0(X0,sK2))) ) | (spl3_3 | ~spl3_7 | ~spl3_14)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f54,f73,f106])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl3_14),
% 0.22/0.48    inference(avatar_component_clause,[],[f105])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) ) | ~spl3_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f72])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    ~r1_xboole_0(sK1,sK2) | spl3_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f53])).
% 0.22/0.48  fof(f155,plain,(
% 0.22/0.48    spl3_20 | ~spl3_6 | ~spl3_10 | ~spl3_15),
% 0.22/0.48    inference(avatar_split_clause,[],[f135,f117,f84,f68,f152])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    spl3_6 <=> ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    spl3_10 <=> ! [X1,X0] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.48  fof(f117,plain,(
% 0.22/0.48    spl3_15 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.48  fof(f135,plain,(
% 0.22/0.48    r1_tarski(sK1,sK0) | (~spl3_6 | ~spl3_10 | ~spl3_15)),
% 0.22/0.48    inference(forward_demodulation,[],[f133,f69])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) ) | ~spl3_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f68])).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    r1_tarski(sK1,k3_tarski(k1_zfmisc_1(sK0))) | (~spl3_10 | ~spl3_15)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f119,f85])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) ) | ~spl3_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f84])).
% 0.22/0.48  fof(f119,plain,(
% 0.22/0.48    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_15),
% 0.22/0.48    inference(avatar_component_clause,[],[f117])).
% 0.22/0.48  fof(f128,plain,(
% 0.22/0.48    spl3_17),
% 0.22/0.48    inference(avatar_split_clause,[],[f41,f126])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(flattening,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    spl3_16),
% 0.22/0.48    inference(avatar_split_clause,[],[f39,f122])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    spl3_15 | ~spl3_1 | ~spl3_5 | ~spl3_11),
% 0.22/0.48    inference(avatar_split_clause,[],[f108,f88,f64,f43,f117])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    spl3_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    spl3_5 <=> ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    spl3_11 <=> ! [X1,X0] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    r2_hidden(sK1,k1_zfmisc_1(sK0)) | (~spl3_1 | ~spl3_5 | ~spl3_11)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f65,f45,f89])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) ) | ~spl3_11),
% 0.22/0.48    inference(avatar_component_clause,[],[f88])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f43])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) ) | ~spl3_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f64])).
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    spl3_14),
% 0.22/0.48    inference(avatar_split_clause,[],[f40,f105])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(flattening,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    spl3_11),
% 0.22/0.48    inference(avatar_split_clause,[],[f34,f88])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.22/0.48    inference(nnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    spl3_10),
% 0.22/0.48    inference(avatar_split_clause,[],[f38,f84])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    spl3_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f32,f72])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    spl3_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f31,f68])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    spl3_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f30,f64])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    ~spl3_3 | ~spl3_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f61,f57,f53])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    ~r1_xboole_0(sK1,sK2) | ~spl3_4),
% 0.22/0.48    inference(subsumption_resolution,[],[f29,f59])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(sK1,sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ((~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(sK1,sK2)) & (r1_tarski(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f23,f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(sK1,k3_subset_1(sK0,X2)) | ~r1_xboole_0(sK1,X2)) & (r1_tarski(sK1,k3_subset_1(sK0,X2)) | r1_xboole_0(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ? [X2] : ((~r1_tarski(sK1,k3_subset_1(sK0,X2)) | ~r1_xboole_0(sK1,X2)) & (r1_tarski(sK1,k3_subset_1(sK0,X2)) | r1_xboole_0(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(sK1,sK2)) & (r1_tarski(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(flattening,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ? [X0,X1] : (? [X2] : (((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(nnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ? [X0,X1] : (? [X2] : ((r1_xboole_0(X1,X2) <~> r1_tarski(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.22/0.48    inference(negated_conjecture,[],[f10])).
% 0.22/0.48  fof(f10,conjecture,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    spl3_3 | spl3_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f28,f57,f53])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    r1_tarski(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    spl3_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f27,f48])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    spl3_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f26,f43])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (8261)------------------------------
% 0.22/0.48  % (8261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (8261)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (8261)Memory used [KB]: 6140
% 0.22/0.48  % (8261)Time elapsed: 0.055 s
% 0.22/0.48  % (8261)------------------------------
% 0.22/0.48  % (8261)------------------------------
% 0.22/0.48  % (8262)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (8255)Success in time 0.113 s
%------------------------------------------------------------------------------
