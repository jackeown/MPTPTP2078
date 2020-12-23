%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 208 expanded)
%              Number of leaves         :   22 (  72 expanded)
%              Depth                    :   14
%              Number of atoms          :  249 ( 482 expanded)
%              Number of equality atoms :   62 ( 155 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f188,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f71,f75,f82,f91,f118,f140,f146,f149,f183])).

fof(f183,plain,
    ( ~ spl3_3
    | spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f181,f144,f80,f73])).

fof(f73,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f80,plain,
    ( spl3_4
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f144,plain,
    ( spl3_8
  <=> k3_subset_1(sK0,sK1) = k1_subset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f181,plain,
    ( sK0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f175,f56])).

fof(f56,plain,(
    ! [X0] : k3_subset_1(X0,k1_subset_1(X0)) = X0 ),
    inference(definition_unfolding,[],[f37,f39])).

fof(f39,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f37,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f175,plain,
    ( sK1 = k3_subset_1(sK0,k1_subset_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_8 ),
    inference(superposition,[],[f44,f145])).

fof(f145,plain,
    ( k3_subset_1(sK0,sK1) = k1_subset_1(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f144])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f149,plain,
    ( ~ spl3_4
    | spl3_2 ),
    inference(avatar_split_clause,[],[f147,f66,f80])).

fof(f66,plain,
    ( spl3_2
  <=> sK1 = k3_subset_1(sK0,k1_subset_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f147,plain,
    ( sK0 != sK1
    | spl3_2 ),
    inference(forward_demodulation,[],[f67,f56])).

fof(f67,plain,
    ( sK1 != k3_subset_1(sK0,k1_subset_1(sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f146,plain,
    ( ~ spl3_1
    | spl3_8
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f122,f73,f144,f63])).

fof(f63,plain,
    ( spl3_1
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f122,plain,
    ( k3_subset_1(sK0,sK1) = k1_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f107,f74])).

fof(f74,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f107,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | k3_subset_1(X1,X2) = k1_subset_1(X1)
      | ~ r1_tarski(k3_subset_1(X1,X2),X2) ) ),
    inference(global_subsumption,[],[f42,f106])).

fof(f106,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k3_subset_1(X1,X2),X2)
      | k3_subset_1(X1,X2) = k1_subset_1(X1)
      | ~ m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ) ),
    inference(superposition,[],[f45,f44])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_subset_1(X0) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(X1,k3_subset_1(X0,X1))
          | k1_subset_1(X0) != X1 )
        & ( k1_subset_1(X0) = X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f140,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | spl3_7 ),
    inference(subsumption_resolution,[],[f117,f137])).

fof(f137,plain,(
    ! [X0] : r1_tarski(k5_xboole_0(X0,X0),X0) ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,(
    ! [X0] :
      ( r1_tarski(k5_xboole_0(X0,X0),X0)
      | r1_tarski(k5_xboole_0(X0,X0),X0) ) ),
    inference(resolution,[],[f128,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f128,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(sK2(X1,X2),k5_xboole_0(X2,X2))
      | r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f121,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ r2_hidden(sK2(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f47,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f121,plain,(
    ! [X2] : m1_subset_1(k5_xboole_0(X2,X2),k1_zfmisc_1(X2)) ),
    inference(global_subsumption,[],[f76,f114])).

fof(f114,plain,(
    ! [X2] :
      ( m1_subset_1(k5_xboole_0(X2,X2),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f42,f110])).

fof(f110,plain,(
    ! [X0] : k3_subset_1(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(global_subsumption,[],[f76,f109])).

fof(f109,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X0) = k5_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f108,f60])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f58,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f43,f40])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f76,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f57,f56])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_subset_1(X0)),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f117,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK0),sK0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl3_7
  <=> r1_tarski(k5_xboole_0(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f118,plain,
    ( ~ spl3_7
    | spl3_6 ),
    inference(avatar_split_clause,[],[f111,f89,f116])).

fof(f89,plain,
    ( spl3_6
  <=> r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f111,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK0),sK0)
    | spl3_6 ),
    inference(superposition,[],[f90,f110])).

fof(f90,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f91,plain,
    ( ~ spl3_6
    | spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f87,f80,f63,f89])).

fof(f87,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl3_1
    | ~ spl3_4 ),
    inference(superposition,[],[f64,f81])).

fof(f81,plain,
    ( sK0 = sK1
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f64,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f82,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f78,f66,f80])).

fof(f78,plain,
    ( sK0 = sK1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f70,f56])).

fof(f70,plain,
    ( sK1 = k3_subset_1(sK0,k1_subset_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f75,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f34,f73])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( sK1 != k2_subset_1(sK0)
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( sK1 = k2_subset_1(sK0)
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k2_subset_1(sK0)
        | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & ( sK1 = k2_subset_1(sK0)
        | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

% (15072)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f23,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

fof(f71,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f55,f66,f63])).

fof(f55,plain,
    ( sK1 = k3_subset_1(sK0,k1_subset_1(sK0))
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f35,f39])).

fof(f35,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f68,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f54,f66,f63])).

fof(f54,plain,
    ( sK1 != k3_subset_1(sK0,k1_subset_1(sK0))
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f36,f39])).

fof(f36,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:38:03 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (15059)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (15061)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (15061)Refutation not found, incomplete strategy% (15061)------------------------------
% 0.21/0.51  % (15061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15061)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (15061)Memory used [KB]: 6268
% 0.21/0.51  % (15061)Time elapsed: 0.098 s
% 0.21/0.51  % (15061)------------------------------
% 0.21/0.51  % (15061)------------------------------
% 0.21/0.51  % (15059)Refutation not found, incomplete strategy% (15059)------------------------------
% 0.21/0.51  % (15059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15059)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (15059)Memory used [KB]: 10618
% 0.21/0.51  % (15059)Time elapsed: 0.094 s
% 0.21/0.51  % (15059)------------------------------
% 0.21/0.51  % (15059)------------------------------
% 0.21/0.51  % (15065)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (15076)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (15063)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (15076)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (15064)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f188,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f68,f71,f75,f82,f91,f118,f140,f146,f149,f183])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    ~spl3_3 | spl3_4 | ~spl3_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f181,f144,f80,f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    spl3_4 <=> sK0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    spl3_8 <=> k3_subset_1(sK0,sK1) = k1_subset_1(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.52  fof(f181,plain,(
% 0.21/0.52    sK0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_8),
% 0.21/0.52    inference(forward_demodulation,[],[f175,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0] : (k3_subset_1(X0,k1_subset_1(X0)) = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f37,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.52  fof(f175,plain,(
% 0.21/0.52    sK1 = k3_subset_1(sK0,k1_subset_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_8),
% 0.21/0.52    inference(superposition,[],[f44,f145])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    k3_subset_1(sK0,sK1) = k1_subset_1(sK0) | ~spl3_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f144])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    ~spl3_4 | spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f147,f66,f80])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    spl3_2 <=> sK1 = k3_subset_1(sK0,k1_subset_1(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    sK0 != sK1 | spl3_2),
% 0.21/0.52    inference(forward_demodulation,[],[f67,f56])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    sK1 != k3_subset_1(sK0,k1_subset_1(sK0)) | spl3_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f66])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    ~spl3_1 | spl3_8 | ~spl3_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f122,f73,f144,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    spl3_1 <=> r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    k3_subset_1(sK0,sK1) = k1_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | ~spl3_3),
% 0.21/0.52    inference(resolution,[],[f107,f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f73])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X1)) | k3_subset_1(X1,X2) = k1_subset_1(X1) | ~r1_tarski(k3_subset_1(X1,X2),X2)) )),
% 0.21/0.52    inference(global_subsumption,[],[f42,f106])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    ( ! [X2,X1] : (~r1_tarski(k3_subset_1(X1,X2),X2) | k3_subset_1(X1,X2) = k1_subset_1(X1) | ~m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) )),
% 0.21/0.52    inference(superposition,[],[f45,f44])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : (((r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1) & (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(nnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    spl3_7),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f138])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    $false | spl3_7),
% 0.21/0.52    inference(subsumption_resolution,[],[f117,f137])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k5_xboole_0(X0,X0),X0)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f134])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k5_xboole_0(X0,X0),X0) | r1_tarski(k5_xboole_0(X0,X0),X0)) )),
% 0.21/0.52    inference(resolution,[],[f128,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(rectify,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    ( ! [X2,X1] : (~r2_hidden(sK2(X1,X2),k5_xboole_0(X2,X2)) | r1_tarski(X1,X2)) )),
% 0.21/0.52    inference(resolution,[],[f121,f97])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~r2_hidden(sK2(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(resolution,[],[f47,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    ( ! [X2] : (m1_subset_1(k5_xboole_0(X2,X2),k1_zfmisc_1(X2))) )),
% 0.21/0.52    inference(global_subsumption,[],[f76,f114])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    ( ! [X2] : (m1_subset_1(k5_xboole_0(X2,X2),k1_zfmisc_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X2))) )),
% 0.21/0.52    inference(superposition,[],[f42,f110])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    ( ! [X0] : (k3_subset_1(X0,X0) = k5_xboole_0(X0,X0)) )),
% 0.21/0.52    inference(global_subsumption,[],[f76,f109])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(X0)) | k3_subset_1(X0,X0) = k5_xboole_0(X0,X0)) )),
% 0.21/0.52    inference(resolution,[],[f108,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,X0)) )),
% 0.21/0.52    inference(superposition,[],[f58,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f43,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f57,f56])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_subset_1(X0)),k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f38,f39])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    ~r1_tarski(k5_xboole_0(sK0,sK0),sK0) | spl3_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f116])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    spl3_7 <=> r1_tarski(k5_xboole_0(sK0,sK0),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    ~spl3_7 | spl3_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f111,f89,f116])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    spl3_6 <=> r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    ~r1_tarski(k5_xboole_0(sK0,sK0),sK0) | spl3_6),
% 0.21/0.52    inference(superposition,[],[f90,f110])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | spl3_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f89])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ~spl3_6 | spl3_1 | ~spl3_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f87,f80,f63,f89])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | (spl3_1 | ~spl3_4)),
% 0.21/0.52    inference(superposition,[],[f64,f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    sK0 = sK1 | ~spl3_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f80])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | spl3_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f63])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    spl3_4 | ~spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f78,f66,f80])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    sK0 = sK1 | ~spl3_2),
% 0.21/0.52    inference(forward_demodulation,[],[f70,f56])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    sK1 = k3_subset_1(sK0,k1_subset_1(sK0)) | ~spl3_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f66])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    spl3_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f34,f73])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    (sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(flattening,[],[f23])).
% 0.21/0.52  % (15072)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(nnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.21/0.52    inference(negated_conjecture,[],[f13])).
% 0.21/0.52  fof(f13,conjecture,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    spl3_1 | spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f55,f66,f63])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    sK1 = k3_subset_1(sK0,k1_subset_1(sK0)) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.52    inference(definition_unfolding,[],[f35,f39])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ~spl3_1 | ~spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f54,f66,f63])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    sK1 != k3_subset_1(sK0,k1_subset_1(sK0)) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.52    inference(definition_unfolding,[],[f36,f39])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (15076)------------------------------
% 0.21/0.52  % (15076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15076)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (15076)Memory used [KB]: 10746
% 0.21/0.52  % (15076)Time elapsed: 0.114 s
% 0.21/0.52  % (15076)------------------------------
% 0.21/0.52  % (15076)------------------------------
% 0.21/0.52  % (15058)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (15056)Success in time 0.164 s
%------------------------------------------------------------------------------
