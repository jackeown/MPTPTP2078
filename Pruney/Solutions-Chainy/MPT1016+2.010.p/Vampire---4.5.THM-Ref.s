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
% DateTime   : Thu Dec  3 13:05:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 385 expanded)
%              Number of leaves         :   33 ( 129 expanded)
%              Depth                    :   16
%              Number of atoms          :  617 (2500 expanded)
%              Number of equality atoms :  123 ( 677 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f624,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f84,f89,f94,f98,f162,f183,f222,f259,f261,f287,f291,f323,f527,f588,f597,f602,f623])).

fof(f623,plain,
    ( spl8_35
    | ~ spl8_36 ),
    inference(avatar_contradiction_clause,[],[f622])).

fof(f622,plain,
    ( $false
    | spl8_35
    | ~ spl8_36 ),
    inference(subsumption_resolution,[],[f621,f49])).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f621,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl8_35
    | ~ spl8_36 ),
    inference(backward_demodulation,[],[f496,f601])).

fof(f601,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f599])).

fof(f599,plain,
    ( spl8_36
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f496,plain,
    ( ~ v1_xboole_0(sK2)
    | spl8_35 ),
    inference(avatar_component_clause,[],[f494])).

fof(f494,plain,
    ( spl8_35
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f602,plain,
    ( spl8_36
    | ~ spl8_4
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f474,f317,f86,f599])).

fof(f86,plain,
    ( spl8_4
  <=> r2_hidden(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f317,plain,
    ( spl8_21
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | ~ v1_funct_2(sK3,X1,X0)
        | ~ r2_hidden(sK5,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f474,plain,
    ( ~ r2_hidden(sK5,sK2)
    | k1_xboole_0 = sK2
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f472,f42])).

fof(f42,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ( sK4 != sK5
        & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
        & r2_hidden(sK5,sK2)
        & r2_hidden(sK4,sK2) )
      | ~ v2_funct_1(sK3) )
    & ( ! [X4,X5] :
          ( X4 = X5
          | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
          | ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(X4,sK2) )
      | v2_funct_1(sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK3,sK2,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f29,f31,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ( ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | ~ v2_funct_1(X1) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X0) )
          | v2_funct_1(X1) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ? [X3,X2] :
            ( X2 != X3
            & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3)
            & r2_hidden(X3,sK2)
            & r2_hidden(X2,sK2) )
        | ~ v2_funct_1(sK3) )
      & ( ! [X5,X4] :
            ( X4 = X5
            | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
            | ~ r2_hidden(X5,sK2)
            | ~ r2_hidden(X4,sK2) )
        | v2_funct_1(sK3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v1_funct_2(sK3,sK2,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X3,X2] :
        ( X2 != X3
        & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3)
        & r2_hidden(X3,sK2)
        & r2_hidden(X2,sK2) )
   => ( sK4 != sK5
      & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
      & r2_hidden(sK5,sK2)
      & r2_hidden(sK4,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
            | ~ r2_hidden(X5,X0)
            | ~ r2_hidden(X4,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).

fof(f472,plain,
    ( ~ v1_funct_2(sK3,sK2,sK2)
    | ~ r2_hidden(sK5,sK2)
    | k1_xboole_0 = sK2
    | ~ spl8_21 ),
    inference(resolution,[],[f318,f43])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f318,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK3,X1,X0)
        | ~ r2_hidden(sK5,X1)
        | k1_xboole_0 = X0 )
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f317])).

fof(f597,plain,
    ( ~ spl8_35
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f539,f86,f494])).

fof(f539,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl8_4 ),
    inference(resolution,[],[f297,f69])).

fof(f69,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f297,plain,
    ( ! [X6] :
        ( ~ r1_tarski(sK2,X6)
        | ~ v1_xboole_0(X6) )
    | ~ spl8_4 ),
    inference(resolution,[],[f88,f123])).

fof(f123,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X2,X3)
      | ~ v1_xboole_0(X1)
      | ~ r1_tarski(X3,X1) ) ),
    inference(resolution,[],[f67,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f88,plain,
    ( r2_hidden(sK5,sK2)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f588,plain,
    ( ~ spl8_1
    | spl8_2
    | ~ spl8_5
    | ~ spl8_22
    | spl8_35 ),
    inference(avatar_contradiction_clause,[],[f587])).

fof(f587,plain,
    ( $false
    | ~ spl8_1
    | spl8_2
    | ~ spl8_5
    | ~ spl8_22
    | spl8_35 ),
    inference(subsumption_resolution,[],[f586,f49])).

fof(f586,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_1
    | spl8_2
    | ~ spl8_5
    | ~ spl8_22
    | spl8_35 ),
    inference(backward_demodulation,[],[f496,f406])).

fof(f406,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_1
    | spl8_2
    | ~ spl8_5
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f405,f42])).

fof(f405,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ spl8_1
    | spl8_2
    | ~ spl8_5
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f403,f93])).

fof(f93,plain,
    ( r2_hidden(sK4,sK2)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl8_5
  <=> r2_hidden(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f403,plain,
    ( ~ r2_hidden(sK4,sK2)
    | k1_xboole_0 = sK2
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ spl8_1
    | spl8_2
    | ~ spl8_22 ),
    inference(resolution,[],[f344,f43])).

fof(f344,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ r2_hidden(sK4,X1)
        | k1_xboole_0 = X0
        | ~ v1_funct_2(sK3,X1,X0) )
    | ~ spl8_1
    | spl8_2
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f343,f41])).

fof(f41,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f343,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | ~ r2_hidden(sK4,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK3,X1,X0)
        | ~ v1_funct_1(sK3) )
    | ~ spl8_1
    | spl8_2
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f342,f73])).

fof(f73,plain,
    ( v2_funct_1(sK3)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl8_1
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f342,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | ~ r2_hidden(sK4,X1)
        | ~ v2_funct_1(sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK3,X1,X0)
        | ~ v1_funct_1(sK3) )
    | spl8_2
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f337,f78])).

fof(f78,plain,
    ( sK4 != sK5
    | spl8_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl8_2
  <=> sK4 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f337,plain,
    ( ! [X0,X1] :
        ( sK4 = sK5
        | k1_xboole_0 = X0
        | ~ r2_hidden(sK4,X1)
        | ~ v2_funct_1(sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK3,X1,X0)
        | ~ v1_funct_1(sK3) )
    | ~ spl8_22 ),
    inference(superposition,[],[f322,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

fof(f322,plain,
    ( sK5 = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4))
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f320])).

fof(f320,plain,
    ( spl8_22
  <=> sK5 = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f527,plain,(
    spl8_15 ),
    inference(avatar_split_clause,[],[f526,f168])).

fof(f168,plain,
    ( spl8_15
  <=> r1_tarski(k1_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f526,plain,(
    r1_tarski(k1_relat_1(sK3),sK2) ),
    inference(resolution,[],[f250,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f250,plain,(
    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f198,f43])).

fof(f198,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f197])).

fof(f197,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f66,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f323,plain,
    ( spl8_21
    | spl8_22
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f315,f81,f72,f320,f317])).

fof(f81,plain,
    ( spl8_3
  <=> k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f315,plain,
    ( ! [X0,X1] :
        ( sK5 = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4))
        | k1_xboole_0 = X0
        | ~ r2_hidden(sK5,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK3,X1,X0) )
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f314,f41])).

fof(f314,plain,
    ( ! [X0,X1] :
        ( sK5 = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4))
        | k1_xboole_0 = X0
        | ~ r2_hidden(sK5,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK3,X1,X0)
        | ~ v1_funct_1(sK3) )
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f311,f73])).

fof(f311,plain,
    ( ! [X0,X1] :
        ( sK5 = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4))
        | k1_xboole_0 = X0
        | ~ r2_hidden(sK5,X1)
        | ~ v2_funct_1(sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK3,X1,X0)
        | ~ v1_funct_1(sK3) )
    | ~ spl8_3 ),
    inference(superposition,[],[f68,f83])).

fof(f83,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f291,plain,
    ( spl8_1
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f186,f151,f72])).

fof(f151,plain,
    ( spl8_12
  <=> sP0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f186,plain,
    ( v2_funct_1(sK3)
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f185,f41])).

fof(f185,plain,
    ( ~ v1_funct_1(sK3)
    | v2_funct_1(sK3)
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f184,f105])).

fof(f105,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f64,f43])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f184,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | v2_funct_1(sK3)
    | ~ spl8_12 ),
    inference(resolution,[],[f153,f99])).

fof(f99,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v2_funct_1(X0) ) ),
    inference(resolution,[],[f57,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ sP0(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_funct_1(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f57,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f16,f25,f24])).

fof(f24,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1,X2] :
          ( X1 = X2
          | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
          | ~ r2_hidden(X2,k1_relat_1(X0))
          | ~ r2_hidden(X1,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

% (9103)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% (9103)Refutation not found, incomplete strategy% (9103)------------------------------
% (9103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9103)Termination reason: Refutation not found, incomplete strategy

% (9103)Memory used [KB]: 6140
% (9103)Time elapsed: 0.140 s
% (9103)------------------------------
% (9103)------------------------------
% (9095)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% (9114)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% (9095)Refutation not found, incomplete strategy% (9095)------------------------------
% (9095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9095)Termination reason: Refutation not found, incomplete strategy

% (9095)Memory used [KB]: 6140
% (9095)Time elapsed: 0.144 s
% (9095)------------------------------
% (9095)------------------------------
% (9096)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% (9096)Refutation not found, incomplete strategy% (9096)------------------------------
% (9096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9096)Termination reason: Refutation not found, incomplete strategy

% (9096)Memory used [KB]: 10618
% (9096)Time elapsed: 0.107 s
% (9096)------------------------------
% (9096)------------------------------
% (9107)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% (9100)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% (9104)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (9092)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
fof(f16,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f153,plain,
    ( sP0(sK3)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f151])).

fof(f287,plain,
    ( spl8_12
    | ~ spl8_18 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | spl8_12
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f285,f152])).

fof(f152,plain,
    ( ~ sP0(sK3)
    | spl8_12 ),
    inference(avatar_component_clause,[],[f151])).

fof(f285,plain,
    ( sP0(sK3)
    | ~ spl8_18 ),
    inference(trivial_inequality_removal,[],[f283])).

fof(f283,plain,
    ( sK6(sK3) != sK6(sK3)
    | sP0(sK3)
    | ~ spl8_18 ),
    inference(superposition,[],[f56,f221])).

fof(f221,plain,
    ( sK7(sK3) = sK6(sK3)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl8_18
  <=> sK7(sK3) = sK6(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f56,plain,(
    ! [X0] :
      ( sK6(X0) != sK7(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( sK6(X0) != sK7(X0)
          & k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0))
          & r2_hidden(sK7(X0),k1_relat_1(X0))
          & r2_hidden(sK6(X0),k1_relat_1(X0)) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f35,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK6(X0) != sK7(X0)
        & k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0))
        & r2_hidden(sK7(X0),k1_relat_1(X0))
        & r2_hidden(sK6(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1,X2] :
            ( X1 != X2
            & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
            & r2_hidden(X2,k1_relat_1(X0))
            & r2_hidden(X1,k1_relat_1(X0)) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1,X2] :
            ( X1 != X2
            & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
            & r2_hidden(X2,k1_relat_1(X0))
            & r2_hidden(X1,k1_relat_1(X0)) ) )
      & ( ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f261,plain,
    ( ~ spl8_15
    | spl8_12
    | spl8_17 ),
    inference(avatar_split_clause,[],[f260,f215,f151,f168])).

fof(f215,plain,
    ( spl8_17
  <=> r2_hidden(sK6(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f260,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK2)
    | spl8_12
    | spl8_17 ),
    inference(subsumption_resolution,[],[f225,f152])).

fof(f225,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK2)
    | sP0(sK3)
    | spl8_17 ),
    inference(resolution,[],[f223,f53])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(sK3),X0)
        | ~ r1_tarski(X0,sK2) )
    | spl8_17 ),
    inference(resolution,[],[f217,f136])).

fof(f136,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(X1,X2)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f58,f63])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f217,plain,
    ( ~ r2_hidden(sK6(sK3),sK2)
    | spl8_17 ),
    inference(avatar_component_clause,[],[f215])).

fof(f259,plain,
    ( ~ spl8_15
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f237,f181,f168])).

fof(f181,plain,
    ( spl8_16
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ r1_tarski(k1_relat_1(sK3),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f237,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK2)
    | ~ spl8_16 ),
    inference(resolution,[],[f182,f69])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK3),X0)
        | ~ r1_tarski(X0,sK2) )
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f181])).

fof(f222,plain,
    ( ~ spl8_17
    | spl8_18
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f213,f159,f219,f215])).

fof(f159,plain,
    ( spl8_14
  <=> ! [X0] :
        ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK6(sK3))
        | sK7(sK3) = X0
        | ~ r2_hidden(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f213,plain,
    ( sK7(sK3) = sK6(sK3)
    | ~ r2_hidden(sK6(sK3),sK2)
    | ~ spl8_14 ),
    inference(equality_resolution,[],[f160])).

fof(f160,plain,
    ( ! [X0] :
        ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK6(sK3))
        | sK7(sK3) = X0
        | ~ r2_hidden(X0,sK2) )
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f159])).

fof(f183,plain,
    ( spl8_12
    | spl8_16
    | spl8_13 ),
    inference(avatar_split_clause,[],[f177,f155,f181,f151])).

fof(f155,plain,
    ( spl8_13
  <=> r2_hidden(sK7(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ r1_tarski(k1_relat_1(sK3),X0)
        | sP0(sK3) )
    | spl8_13 ),
    inference(resolution,[],[f166,f54])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f166,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK7(sK3),X1)
        | ~ r1_tarski(X0,sK2)
        | ~ r1_tarski(X1,X0) )
    | spl8_13 ),
    inference(resolution,[],[f163,f136])).

fof(f163,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK7(sK3),X0)
        | ~ r1_tarski(X0,sK2) )
    | spl8_13 ),
    inference(resolution,[],[f157,f136])).

fof(f157,plain,
    ( ~ r2_hidden(sK7(sK3),sK2)
    | spl8_13 ),
    inference(avatar_component_clause,[],[f155])).

fof(f162,plain,
    ( spl8_12
    | ~ spl8_13
    | spl8_14
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f149,f96,f159,f155,f151])).

fof(f96,plain,
    ( spl8_6
  <=> ! [X5,X4] :
        ( X4 = X5
        | ~ r2_hidden(X4,sK2)
        | ~ r2_hidden(X5,sK2)
        | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f149,plain,
    ( ! [X1] :
        ( k1_funct_1(sK3,X1) != k1_funct_1(sK3,sK6(sK3))
        | ~ r2_hidden(sK7(sK3),sK2)
        | ~ r2_hidden(X1,sK2)
        | sK7(sK3) = X1
        | sP0(sK3) )
    | ~ spl8_6 ),
    inference(superposition,[],[f97,f55])).

fof(f55,plain,(
    ! [X0] :
      ( k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f97,plain,
    ( ! [X4,X5] :
        ( k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
        | ~ r2_hidden(X4,sK2)
        | ~ r2_hidden(X5,sK2)
        | X4 = X5 )
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f98,plain,
    ( spl8_1
    | spl8_6 ),
    inference(avatar_split_clause,[],[f44,f96,f72])).

fof(f44,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK2)
      | v2_funct_1(sK3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f94,plain,
    ( ~ spl8_1
    | spl8_5 ),
    inference(avatar_split_clause,[],[f45,f91,f72])).

fof(f45,plain,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f89,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f46,f86,f72])).

fof(f46,plain,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f47,f81,f72])).

fof(f47,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f48,f76,f72])).

fof(f48,plain,
    ( sK4 != sK5
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:48:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (9091)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (9094)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (9093)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (9090)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (9090)Refutation not found, incomplete strategy% (9090)------------------------------
% 0.22/0.52  % (9090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (9090)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (9090)Memory used [KB]: 10618
% 0.22/0.52  % (9090)Time elapsed: 0.109 s
% 0.22/0.52  % (9090)------------------------------
% 0.22/0.52  % (9090)------------------------------
% 0.22/0.53  % (9101)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.53  % (9102)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.53  % (9101)Refutation not found, incomplete strategy% (9101)------------------------------
% 0.22/0.53  % (9101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (9101)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (9101)Memory used [KB]: 10618
% 0.22/0.53  % (9101)Time elapsed: 0.123 s
% 0.22/0.53  % (9101)------------------------------
% 0.22/0.53  % (9101)------------------------------
% 0.22/0.53  % (9106)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.53  % (9111)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.53  % (9110)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  % (9091)Refutation not found, incomplete strategy% (9091)------------------------------
% 0.22/0.53  % (9091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (9091)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (9091)Memory used [KB]: 10746
% 0.22/0.53  % (9091)Time elapsed: 0.123 s
% 0.22/0.53  % (9091)------------------------------
% 0.22/0.53  % (9091)------------------------------
% 0.22/0.53  % (9115)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.53  % (9108)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.54  % (9097)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.54  % (9099)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.54  % (9112)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.54  % (9098)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.54  % (9105)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.54  % (9094)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f624,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f79,f84,f89,f94,f98,f162,f183,f222,f259,f261,f287,f291,f323,f527,f588,f597,f602,f623])).
% 0.22/0.54  fof(f623,plain,(
% 0.22/0.54    spl8_35 | ~spl8_36),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f622])).
% 0.22/0.54  fof(f622,plain,(
% 0.22/0.54    $false | (spl8_35 | ~spl8_36)),
% 0.22/0.54    inference(subsumption_resolution,[],[f621,f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.54  fof(f621,plain,(
% 0.22/0.54    ~v1_xboole_0(k1_xboole_0) | (spl8_35 | ~spl8_36)),
% 0.22/0.54    inference(backward_demodulation,[],[f496,f601])).
% 0.22/0.54  fof(f601,plain,(
% 0.22/0.54    k1_xboole_0 = sK2 | ~spl8_36),
% 0.22/0.54    inference(avatar_component_clause,[],[f599])).
% 0.22/0.54  fof(f599,plain,(
% 0.22/0.54    spl8_36 <=> k1_xboole_0 = sK2),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).
% 0.22/0.54  fof(f496,plain,(
% 0.22/0.54    ~v1_xboole_0(sK2) | spl8_35),
% 0.22/0.54    inference(avatar_component_clause,[],[f494])).
% 0.22/0.54  fof(f494,plain,(
% 0.22/0.54    spl8_35 <=> v1_xboole_0(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 0.22/0.54  fof(f602,plain,(
% 0.22/0.54    spl8_36 | ~spl8_4 | ~spl8_21),
% 0.22/0.54    inference(avatar_split_clause,[],[f474,f317,f86,f599])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    spl8_4 <=> r2_hidden(sK5,sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.54  fof(f317,plain,(
% 0.22/0.54    spl8_21 <=> ! [X1,X0] : (k1_xboole_0 = X0 | ~v1_funct_2(sK3,X1,X0) | ~r2_hidden(sK5,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.22/0.54  fof(f474,plain,(
% 0.22/0.54    ~r2_hidden(sK5,sK2) | k1_xboole_0 = sK2 | ~spl8_21),
% 0.22/0.54    inference(subsumption_resolution,[],[f472,f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    v1_funct_2(sK3,sK2,sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ((sK4 != sK5 & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK4,sK2)) | ~v2_funct_1(sK3)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f29,f31,f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3) & r2_hidden(X3,sK2) & r2_hidden(X2,sK2)) | ~v2_funct_1(sK3)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3) & r2_hidden(X3,sK2) & r2_hidden(X2,sK2)) => (sK4 != sK5 & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK4,sK2))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.54    inference(rectify,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.54    inference(flattening,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.54    inference(flattening,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.22/0.54    inference(negated_conjecture,[],[f11])).
% 0.22/0.54  fof(f11,conjecture,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).
% 0.22/0.54  fof(f472,plain,(
% 0.22/0.54    ~v1_funct_2(sK3,sK2,sK2) | ~r2_hidden(sK5,sK2) | k1_xboole_0 = sK2 | ~spl8_21),
% 0.22/0.54    inference(resolution,[],[f318,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f318,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK3,X1,X0) | ~r2_hidden(sK5,X1) | k1_xboole_0 = X0) ) | ~spl8_21),
% 0.22/0.54    inference(avatar_component_clause,[],[f317])).
% 0.22/0.54  fof(f597,plain,(
% 0.22/0.54    ~spl8_35 | ~spl8_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f539,f86,f494])).
% 0.22/0.54  fof(f539,plain,(
% 0.22/0.54    ~v1_xboole_0(sK2) | ~spl8_4),
% 0.22/0.54    inference(resolution,[],[f297,f69])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(flattening,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.54  fof(f297,plain,(
% 0.22/0.54    ( ! [X6] : (~r1_tarski(sK2,X6) | ~v1_xboole_0(X6)) ) | ~spl8_4),
% 0.22/0.54    inference(resolution,[],[f88,f123])).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    ( ! [X2,X3,X1] : (~r2_hidden(X2,X3) | ~v1_xboole_0(X1) | ~r1_tarski(X3,X1)) )),
% 0.22/0.54    inference(resolution,[],[f67,f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.54    inference(nnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    r2_hidden(sK5,sK2) | ~spl8_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f86])).
% 0.22/0.54  fof(f588,plain,(
% 0.22/0.54    ~spl8_1 | spl8_2 | ~spl8_5 | ~spl8_22 | spl8_35),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f587])).
% 0.22/0.54  fof(f587,plain,(
% 0.22/0.54    $false | (~spl8_1 | spl8_2 | ~spl8_5 | ~spl8_22 | spl8_35)),
% 0.22/0.54    inference(subsumption_resolution,[],[f586,f49])).
% 0.22/0.54  fof(f586,plain,(
% 0.22/0.54    ~v1_xboole_0(k1_xboole_0) | (~spl8_1 | spl8_2 | ~spl8_5 | ~spl8_22 | spl8_35)),
% 0.22/0.54    inference(backward_demodulation,[],[f496,f406])).
% 0.22/0.54  fof(f406,plain,(
% 0.22/0.54    k1_xboole_0 = sK2 | (~spl8_1 | spl8_2 | ~spl8_5 | ~spl8_22)),
% 0.22/0.54    inference(subsumption_resolution,[],[f405,f42])).
% 0.22/0.54  fof(f405,plain,(
% 0.22/0.54    k1_xboole_0 = sK2 | ~v1_funct_2(sK3,sK2,sK2) | (~spl8_1 | spl8_2 | ~spl8_5 | ~spl8_22)),
% 0.22/0.54    inference(subsumption_resolution,[],[f403,f93])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    r2_hidden(sK4,sK2) | ~spl8_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f91])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    spl8_5 <=> r2_hidden(sK4,sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.22/0.54  fof(f403,plain,(
% 0.22/0.54    ~r2_hidden(sK4,sK2) | k1_xboole_0 = sK2 | ~v1_funct_2(sK3,sK2,sK2) | (~spl8_1 | spl8_2 | ~spl8_22)),
% 0.22/0.54    inference(resolution,[],[f344,f43])).
% 0.22/0.54  fof(f344,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_hidden(sK4,X1) | k1_xboole_0 = X0 | ~v1_funct_2(sK3,X1,X0)) ) | (~spl8_1 | spl8_2 | ~spl8_22)),
% 0.22/0.54    inference(subsumption_resolution,[],[f343,f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    v1_funct_1(sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f343,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r2_hidden(sK4,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK3,X1,X0) | ~v1_funct_1(sK3)) ) | (~spl8_1 | spl8_2 | ~spl8_22)),
% 0.22/0.54    inference(subsumption_resolution,[],[f342,f73])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    v2_funct_1(sK3) | ~spl8_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f72])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    spl8_1 <=> v2_funct_1(sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.54  fof(f342,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r2_hidden(sK4,X1) | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK3,X1,X0) | ~v1_funct_1(sK3)) ) | (spl8_2 | ~spl8_22)),
% 0.22/0.54    inference(subsumption_resolution,[],[f337,f78])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    sK4 != sK5 | spl8_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f76])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    spl8_2 <=> sK4 = sK5),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.54  fof(f337,plain,(
% 0.22/0.54    ( ! [X0,X1] : (sK4 = sK5 | k1_xboole_0 = X0 | ~r2_hidden(sK4,X1) | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK3,X1,X0) | ~v1_funct_1(sK3)) ) | ~spl8_22),
% 0.22/0.54    inference(superposition,[],[f322,f68])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.54    inference(flattening,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).
% 0.22/0.54  fof(f322,plain,(
% 0.22/0.54    sK5 = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) | ~spl8_22),
% 0.22/0.54    inference(avatar_component_clause,[],[f320])).
% 0.22/0.54  fof(f320,plain,(
% 0.22/0.54    spl8_22 <=> sK5 = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.22/0.54  fof(f527,plain,(
% 0.22/0.54    spl8_15),
% 0.22/0.54    inference(avatar_split_clause,[],[f526,f168])).
% 0.22/0.54  fof(f168,plain,(
% 0.22/0.54    spl8_15 <=> r1_tarski(k1_relat_1(sK3),sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.22/0.54  fof(f526,plain,(
% 0.22/0.54    r1_tarski(k1_relat_1(sK3),sK2)),
% 0.22/0.54    inference(resolution,[],[f250,f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f250,plain,(
% 0.22/0.54    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2))),
% 0.22/0.54    inference(resolution,[],[f198,f43])).
% 0.22/0.54  fof(f198,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f197])).
% 0.22/0.54  fof(f197,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(superposition,[],[f66,f65])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.22/0.54  fof(f323,plain,(
% 0.22/0.54    spl8_21 | spl8_22 | ~spl8_1 | ~spl8_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f315,f81,f72,f320,f317])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    spl8_3 <=> k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.54  fof(f315,plain,(
% 0.22/0.54    ( ! [X0,X1] : (sK5 = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) | k1_xboole_0 = X0 | ~r2_hidden(sK5,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK3,X1,X0)) ) | (~spl8_1 | ~spl8_3)),
% 0.22/0.54    inference(subsumption_resolution,[],[f314,f41])).
% 0.22/0.55  fof(f314,plain,(
% 0.22/0.55    ( ! [X0,X1] : (sK5 = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) | k1_xboole_0 = X0 | ~r2_hidden(sK5,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK3,X1,X0) | ~v1_funct_1(sK3)) ) | (~spl8_1 | ~spl8_3)),
% 0.22/0.55    inference(subsumption_resolution,[],[f311,f73])).
% 0.22/0.55  fof(f311,plain,(
% 0.22/0.55    ( ! [X0,X1] : (sK5 = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) | k1_xboole_0 = X0 | ~r2_hidden(sK5,X1) | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK3,X1,X0) | ~v1_funct_1(sK3)) ) | ~spl8_3),
% 0.22/0.55    inference(superposition,[],[f68,f83])).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) | ~spl8_3),
% 0.22/0.55    inference(avatar_component_clause,[],[f81])).
% 0.22/0.55  fof(f291,plain,(
% 0.22/0.55    spl8_1 | ~spl8_12),
% 0.22/0.55    inference(avatar_split_clause,[],[f186,f151,f72])).
% 0.22/0.55  fof(f151,plain,(
% 0.22/0.55    spl8_12 <=> sP0(sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.22/0.55  fof(f186,plain,(
% 0.22/0.55    v2_funct_1(sK3) | ~spl8_12),
% 0.22/0.55    inference(subsumption_resolution,[],[f185,f41])).
% 0.22/0.55  fof(f185,plain,(
% 0.22/0.55    ~v1_funct_1(sK3) | v2_funct_1(sK3) | ~spl8_12),
% 0.22/0.55    inference(subsumption_resolution,[],[f184,f105])).
% 0.22/0.55  fof(f105,plain,(
% 0.22/0.55    v1_relat_1(sK3)),
% 0.22/0.55    inference(resolution,[],[f64,f43])).
% 0.22/0.55  fof(f64,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.55  fof(f184,plain,(
% 0.22/0.55    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | v2_funct_1(sK3) | ~spl8_12),
% 0.22/0.55    inference(resolution,[],[f153,f99])).
% 0.22/0.55  fof(f99,plain,(
% 0.22/0.55    ( ! [X0] : (~sP0(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | v2_funct_1(X0)) )),
% 0.22/0.55    inference(resolution,[],[f57,f51])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    ( ! [X0] : (~sP1(X0) | ~sP0(X0) | v2_funct_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ! [X0] : (((v2_funct_1(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_funct_1(X0))) | ~sP1(X0))),
% 0.22/0.55    inference(nnf_transformation,[],[f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ! [X0] : ((v2_funct_1(X0) <=> sP0(X0)) | ~sP1(X0))),
% 0.22/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    ( ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(definition_folding,[],[f16,f25,f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ! [X0] : (sP0(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))),
% 0.22/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.55  % (9103)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (9103)Refutation not found, incomplete strategy% (9103)------------------------------
% 0.22/0.55  % (9103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (9103)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (9103)Memory used [KB]: 6140
% 0.22/0.55  % (9103)Time elapsed: 0.140 s
% 0.22/0.55  % (9103)------------------------------
% 0.22/0.55  % (9103)------------------------------
% 0.22/0.55  % (9095)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.55  % (9114)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.55  % (9095)Refutation not found, incomplete strategy% (9095)------------------------------
% 0.22/0.55  % (9095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (9095)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (9095)Memory used [KB]: 6140
% 0.22/0.55  % (9095)Time elapsed: 0.144 s
% 0.22/0.55  % (9095)------------------------------
% 0.22/0.55  % (9095)------------------------------
% 0.22/0.55  % (9096)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.55  % (9096)Refutation not found, incomplete strategy% (9096)------------------------------
% 0.22/0.55  % (9096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (9096)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (9096)Memory used [KB]: 10618
% 0.22/0.55  % (9096)Time elapsed: 0.107 s
% 0.22/0.55  % (9096)------------------------------
% 0.22/0.55  % (9096)------------------------------
% 0.22/0.55  % (9107)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.56  % (9100)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.56  % (9104)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.56  % (9092)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(flattening,[],[f15])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 0.22/0.56  fof(f153,plain,(
% 0.22/0.56    sP0(sK3) | ~spl8_12),
% 0.22/0.56    inference(avatar_component_clause,[],[f151])).
% 0.22/0.56  fof(f287,plain,(
% 0.22/0.56    spl8_12 | ~spl8_18),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f286])).
% 0.22/0.56  fof(f286,plain,(
% 0.22/0.56    $false | (spl8_12 | ~spl8_18)),
% 0.22/0.56    inference(subsumption_resolution,[],[f285,f152])).
% 0.22/0.56  fof(f152,plain,(
% 0.22/0.56    ~sP0(sK3) | spl8_12),
% 0.22/0.56    inference(avatar_component_clause,[],[f151])).
% 0.22/0.56  fof(f285,plain,(
% 0.22/0.56    sP0(sK3) | ~spl8_18),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f283])).
% 0.22/0.56  fof(f283,plain,(
% 0.22/0.56    sK6(sK3) != sK6(sK3) | sP0(sK3) | ~spl8_18),
% 0.22/0.56    inference(superposition,[],[f56,f221])).
% 0.22/0.56  fof(f221,plain,(
% 0.22/0.56    sK7(sK3) = sK6(sK3) | ~spl8_18),
% 0.22/0.56    inference(avatar_component_clause,[],[f219])).
% 0.22/0.56  fof(f219,plain,(
% 0.22/0.56    spl8_18 <=> sK7(sK3) = sK6(sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ( ! [X0] : (sK6(X0) != sK7(X0) | sP0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f37])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ! [X0] : ((sP0(X0) | (sK6(X0) != sK7(X0) & k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0)) & r2_hidden(sK7(X0),k1_relat_1(X0)) & r2_hidden(sK6(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f35,f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK6(X0) != sK7(X0) & k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0)) & r2_hidden(sK7(X0),k1_relat_1(X0)) & r2_hidden(sK6(X0),k1_relat_1(X0))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 0.22/0.56    inference(rectify,[],[f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~sP0(X0)))),
% 0.22/0.56    inference(nnf_transformation,[],[f24])).
% 0.22/0.56  fof(f261,plain,(
% 0.22/0.56    ~spl8_15 | spl8_12 | spl8_17),
% 0.22/0.56    inference(avatar_split_clause,[],[f260,f215,f151,f168])).
% 0.22/0.56  fof(f215,plain,(
% 0.22/0.56    spl8_17 <=> r2_hidden(sK6(sK3),sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.22/0.56  fof(f260,plain,(
% 0.22/0.56    ~r1_tarski(k1_relat_1(sK3),sK2) | (spl8_12 | spl8_17)),
% 0.22/0.56    inference(subsumption_resolution,[],[f225,f152])).
% 0.22/0.56  fof(f225,plain,(
% 0.22/0.56    ~r1_tarski(k1_relat_1(sK3),sK2) | sP0(sK3) | spl8_17),
% 0.22/0.56    inference(resolution,[],[f223,f53])).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    ( ! [X0] : (r2_hidden(sK6(X0),k1_relat_1(X0)) | sP0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f37])).
% 0.22/0.56  fof(f223,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(sK6(sK3),X0) | ~r1_tarski(X0,sK2)) ) | spl8_17),
% 0.22/0.56    inference(resolution,[],[f217,f136])).
% 0.22/0.56  fof(f136,plain,(
% 0.22/0.56    ( ! [X2,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(X1,X2) | ~r1_tarski(X2,X3)) )),
% 0.22/0.56    inference(resolution,[],[f58,f63])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.56  fof(f217,plain,(
% 0.22/0.56    ~r2_hidden(sK6(sK3),sK2) | spl8_17),
% 0.22/0.56    inference(avatar_component_clause,[],[f215])).
% 0.22/0.56  fof(f259,plain,(
% 0.22/0.56    ~spl8_15 | ~spl8_16),
% 0.22/0.56    inference(avatar_split_clause,[],[f237,f181,f168])).
% 0.22/0.56  fof(f181,plain,(
% 0.22/0.56    spl8_16 <=> ! [X0] : (~r1_tarski(X0,sK2) | ~r1_tarski(k1_relat_1(sK3),X0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.22/0.56  fof(f237,plain,(
% 0.22/0.56    ~r1_tarski(k1_relat_1(sK3),sK2) | ~spl8_16),
% 0.22/0.56    inference(resolution,[],[f182,f69])).
% 0.22/0.56  fof(f182,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_tarski(k1_relat_1(sK3),X0) | ~r1_tarski(X0,sK2)) ) | ~spl8_16),
% 0.22/0.56    inference(avatar_component_clause,[],[f181])).
% 0.22/0.56  fof(f222,plain,(
% 0.22/0.56    ~spl8_17 | spl8_18 | ~spl8_14),
% 0.22/0.56    inference(avatar_split_clause,[],[f213,f159,f219,f215])).
% 0.22/0.56  fof(f159,plain,(
% 0.22/0.56    spl8_14 <=> ! [X0] : (k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK6(sK3)) | sK7(sK3) = X0 | ~r2_hidden(X0,sK2))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.22/0.56  fof(f213,plain,(
% 0.22/0.56    sK7(sK3) = sK6(sK3) | ~r2_hidden(sK6(sK3),sK2) | ~spl8_14),
% 0.22/0.56    inference(equality_resolution,[],[f160])).
% 0.22/0.56  fof(f160,plain,(
% 0.22/0.56    ( ! [X0] : (k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK6(sK3)) | sK7(sK3) = X0 | ~r2_hidden(X0,sK2)) ) | ~spl8_14),
% 0.22/0.56    inference(avatar_component_clause,[],[f159])).
% 0.22/0.56  fof(f183,plain,(
% 0.22/0.56    spl8_12 | spl8_16 | spl8_13),
% 0.22/0.56    inference(avatar_split_clause,[],[f177,f155,f181,f151])).
% 0.22/0.56  fof(f155,plain,(
% 0.22/0.56    spl8_13 <=> r2_hidden(sK7(sK3),sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.22/0.56  fof(f177,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_tarski(X0,sK2) | ~r1_tarski(k1_relat_1(sK3),X0) | sP0(sK3)) ) | spl8_13),
% 0.22/0.56    inference(resolution,[],[f166,f54])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    ( ! [X0] : (r2_hidden(sK7(X0),k1_relat_1(X0)) | sP0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f37])).
% 0.22/0.56  fof(f166,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(sK7(sK3),X1) | ~r1_tarski(X0,sK2) | ~r1_tarski(X1,X0)) ) | spl8_13),
% 0.22/0.56    inference(resolution,[],[f163,f136])).
% 0.22/0.56  fof(f163,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(sK7(sK3),X0) | ~r1_tarski(X0,sK2)) ) | spl8_13),
% 0.22/0.56    inference(resolution,[],[f157,f136])).
% 0.22/0.56  fof(f157,plain,(
% 0.22/0.56    ~r2_hidden(sK7(sK3),sK2) | spl8_13),
% 0.22/0.56    inference(avatar_component_clause,[],[f155])).
% 0.22/0.56  fof(f162,plain,(
% 0.22/0.56    spl8_12 | ~spl8_13 | spl8_14 | ~spl8_6),
% 0.22/0.56    inference(avatar_split_clause,[],[f149,f96,f159,f155,f151])).
% 0.22/0.56  fof(f96,plain,(
% 0.22/0.56    spl8_6 <=> ! [X5,X4] : (X4 = X5 | ~r2_hidden(X4,sK2) | ~r2_hidden(X5,sK2) | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.22/0.56  fof(f149,plain,(
% 0.22/0.56    ( ! [X1] : (k1_funct_1(sK3,X1) != k1_funct_1(sK3,sK6(sK3)) | ~r2_hidden(sK7(sK3),sK2) | ~r2_hidden(X1,sK2) | sK7(sK3) = X1 | sP0(sK3)) ) | ~spl8_6),
% 0.22/0.56    inference(superposition,[],[f97,f55])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    ( ! [X0] : (k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0)) | sP0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f37])).
% 0.22/0.56  fof(f97,plain,(
% 0.22/0.56    ( ! [X4,X5] : (k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X4,sK2) | ~r2_hidden(X5,sK2) | X4 = X5) ) | ~spl8_6),
% 0.22/0.56    inference(avatar_component_clause,[],[f96])).
% 0.22/0.56  fof(f98,plain,(
% 0.22/0.56    spl8_1 | spl8_6),
% 0.22/0.56    inference(avatar_split_clause,[],[f44,f96,f72])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2) | v2_funct_1(sK3)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f94,plain,(
% 0.22/0.56    ~spl8_1 | spl8_5),
% 0.22/0.56    inference(avatar_split_clause,[],[f45,f91,f72])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    r2_hidden(sK4,sK2) | ~v2_funct_1(sK3)),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f89,plain,(
% 0.22/0.56    ~spl8_1 | spl8_4),
% 0.22/0.56    inference(avatar_split_clause,[],[f46,f86,f72])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    r2_hidden(sK5,sK2) | ~v2_funct_1(sK3)),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f84,plain,(
% 0.22/0.56    ~spl8_1 | spl8_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f47,f81,f72])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) | ~v2_funct_1(sK3)),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f79,plain,(
% 0.22/0.56    ~spl8_1 | ~spl8_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f48,f76,f72])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    sK4 != sK5 | ~v2_funct_1(sK3)),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (9094)------------------------------
% 0.22/0.56  % (9094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (9094)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (9094)Memory used [KB]: 6396
% 0.22/0.56  % (9094)Time elapsed: 0.138 s
% 0.22/0.56  % (9094)------------------------------
% 0.22/0.56  % (9094)------------------------------
% 0.22/0.56  % (9087)Success in time 0.2 s
%------------------------------------------------------------------------------
