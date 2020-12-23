%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0667+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 342 expanded)
%              Number of leaves         :   20 (  98 expanded)
%              Depth                    :   15
%              Number of atoms          :  468 (1571 expanded)
%              Number of equality atoms :   70 ( 232 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f223,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f76,f80,f100,f107,f124,f131,f150,f174,f187,f211,f222])).

fof(f222,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f220,f59])).

fof(f59,plain,
    ( v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl5_1
  <=> v1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f220,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl5_2
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f219,f63])).

fof(f63,plain,
    ( v1_funct_1(k7_relat_1(sK1,sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl5_2
  <=> v1_funct_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f219,plain,
    ( ~ v1_funct_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f218,f34])).

fof(f34,plain,(
    ~ v2_funct_1(k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ v2_funct_1(k7_relat_1(sK1,sK0))
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ~ v2_funct_1(k7_relat_1(X1,X0))
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ v2_funct_1(k7_relat_1(sK1,sK0))
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ~ v2_funct_1(k7_relat_1(X1,X0))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ~ v2_funct_1(k7_relat_1(X1,X0))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => v2_funct_1(k7_relat_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => v2_funct_1(k7_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_funct_1)).

fof(f218,plain,
    ( v2_funct_1(k7_relat_1(sK1,sK0))
    | ~ v1_funct_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl5_10 ),
    inference(trivial_inequality_removal,[],[f217])).

fof(f217,plain,
    ( sK2(k7_relat_1(sK1,sK0)) != sK2(k7_relat_1(sK1,sK0))
    | v2_funct_1(k7_relat_1(sK1,sK0))
    | ~ v1_funct_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl5_10 ),
    inference(superposition,[],[f42,f182])).

fof(f182,plain,
    ( sK2(k7_relat_1(sK1,sK0)) = sK3(k7_relat_1(sK1,sK0))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl5_10
  <=> sK2(k7_relat_1(sK1,sK0)) = sK3(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f42,plain,(
    ! [X0] :
      ( sK2(X0) != sK3(X0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK2(X0) != sK3(X0)
            & k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0))
            & r2_hidden(sK3(X0),k1_relat_1(X0))
            & r2_hidden(sK2(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f23,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK2(X0) != sK3(X0)
        & k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0))
        & r2_hidden(sK3(X0),k1_relat_1(X0))
        & r2_hidden(sK2(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
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
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
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
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f211,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | spl5_11 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | spl5_11 ),
    inference(subsumption_resolution,[],[f209,f59])).

fof(f209,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl5_2
    | spl5_11 ),
    inference(subsumption_resolution,[],[f208,f63])).

fof(f208,plain,
    ( ~ v1_funct_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl5_11 ),
    inference(subsumption_resolution,[],[f204,f34])).

fof(f204,plain,
    ( v2_funct_1(k7_relat_1(sK1,sK0))
    | ~ v1_funct_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl5_11 ),
    inference(resolution,[],[f194,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f194,plain,
    ( ! [X0] : ~ r2_hidden(sK2(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,X0)))
    | spl5_11 ),
    inference(subsumption_resolution,[],[f193,f31])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f193,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,X0)))
        | ~ v1_relat_1(sK1) )
    | spl5_11 ),
    inference(superposition,[],[f188,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f188,plain,
    ( ! [X0] : ~ r2_hidden(sK2(k7_relat_1(sK1,sK0)),k3_xboole_0(k1_relat_1(sK1),X0))
    | spl5_11 ),
    inference(resolution,[],[f186,f53])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f186,plain,
    ( ~ r2_hidden(sK2(k7_relat_1(sK1,sK0)),k1_relat_1(sK1))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl5_11
  <=> r2_hidden(sK2(k7_relat_1(sK1,sK0)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f187,plain,
    ( spl5_10
    | ~ spl5_11
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f178,f144,f184,f180])).

fof(f144,plain,
    ( spl5_9
  <=> ! [X0] :
        ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK2(k7_relat_1(sK1,sK0)))
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | sK3(k7_relat_1(sK1,sK0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f178,plain,
    ( ~ r2_hidden(sK2(k7_relat_1(sK1,sK0)),k1_relat_1(sK1))
    | sK2(k7_relat_1(sK1,sK0)) = sK3(k7_relat_1(sK1,sK0))
    | ~ spl5_9 ),
    inference(equality_resolution,[],[f145])).

fof(f145,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK2(k7_relat_1(sK1,sK0)))
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | sK3(k7_relat_1(sK1,sK0)) = X0 )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f144])).

fof(f174,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | spl5_8 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | spl5_8 ),
    inference(subsumption_resolution,[],[f172,f59])).

fof(f172,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl5_2
    | spl5_8 ),
    inference(subsumption_resolution,[],[f171,f63])).

fof(f171,plain,
    ( ~ v1_funct_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl5_8 ),
    inference(subsumption_resolution,[],[f167,f34])).

fof(f167,plain,
    ( v2_funct_1(k7_relat_1(sK1,sK0))
    | ~ v1_funct_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl5_8 ),
    inference(resolution,[],[f157,f40])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f157,plain,
    ( ! [X0] : ~ r2_hidden(sK3(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,X0)))
    | spl5_8 ),
    inference(subsumption_resolution,[],[f156,f31])).

fof(f156,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,X0)))
        | ~ v1_relat_1(sK1) )
    | spl5_8 ),
    inference(superposition,[],[f151,f50])).

fof(f151,plain,
    ( ! [X0] : ~ r2_hidden(sK3(k7_relat_1(sK1,sK0)),k3_xboole_0(k1_relat_1(sK1),X0))
    | spl5_8 ),
    inference(resolution,[],[f142,f53])).

fof(f142,plain,
    ( ~ r2_hidden(sK3(k7_relat_1(sK1,sK0)),k1_relat_1(sK1))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl5_8
  <=> r2_hidden(sK3(k7_relat_1(sK1,sK0)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f150,plain,
    ( ~ spl5_8
    | spl5_9
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f149,f120,f144,f140])).

fof(f120,plain,
    ( spl5_7
  <=> k1_funct_1(sK1,sK3(k7_relat_1(sK1,sK0))) = k1_funct_1(sK1,sK2(k7_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f149,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,X1) != k1_funct_1(sK1,sK2(k7_relat_1(sK1,sK0)))
        | sK3(k7_relat_1(sK1,sK0)) = X1
        | ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ r2_hidden(sK3(k7_relat_1(sK1,sK0)),k1_relat_1(sK1)) )
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f148,f31])).

fof(f148,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,X1) != k1_funct_1(sK1,sK2(k7_relat_1(sK1,sK0)))
        | sK3(k7_relat_1(sK1,sK0)) = X1
        | ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ r2_hidden(sK3(k7_relat_1(sK1,sK0)),k1_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f147,f32])).

fof(f32,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f147,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,X1) != k1_funct_1(sK1,sK2(k7_relat_1(sK1,sK0)))
        | sK3(k7_relat_1(sK1,sK0)) = X1
        | ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ r2_hidden(sK3(k7_relat_1(sK1,sK0)),k1_relat_1(sK1))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f135,f33])).

fof(f33,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f135,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,X1) != k1_funct_1(sK1,sK2(k7_relat_1(sK1,sK0)))
        | sK3(k7_relat_1(sK1,sK0)) = X1
        | ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ r2_hidden(sK3(k7_relat_1(sK1,sK0)),k1_relat_1(sK1))
        | ~ v2_funct_1(sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl5_7 ),
    inference(superposition,[],[f38,f122])).

fof(f122,plain,
    ( k1_funct_1(sK1,sK3(k7_relat_1(sK1,sK0))) = k1_funct_1(sK1,sK2(k7_relat_1(sK1,sK0)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f120])).

fof(f38,plain,(
    ! [X4,X0,X3] :
      ( k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f131,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | spl5_6 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | spl5_6 ),
    inference(subsumption_resolution,[],[f129,f59])).

fof(f129,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl5_2
    | spl5_6 ),
    inference(subsumption_resolution,[],[f128,f63])).

fof(f128,plain,
    ( ~ v1_funct_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl5_6 ),
    inference(subsumption_resolution,[],[f125,f34])).

fof(f125,plain,
    ( v2_funct_1(k7_relat_1(sK1,sK0))
    | ~ v1_funct_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl5_6 ),
    inference(resolution,[],[f118,f39])).

fof(f118,plain,
    ( ~ r2_hidden(sK2(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0)))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl5_6
  <=> r2_hidden(sK2(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f124,plain,
    ( ~ spl5_6
    | spl5_7
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f112,f96,f120,f116])).

fof(f96,plain,
    ( spl5_5
  <=> k1_funct_1(k7_relat_1(sK1,sK0),sK2(k7_relat_1(sK1,sK0))) = k1_funct_1(sK1,sK3(k7_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f112,plain,
    ( k1_funct_1(sK1,sK3(k7_relat_1(sK1,sK0))) = k1_funct_1(sK1,sK2(k7_relat_1(sK1,sK0)))
    | ~ r2_hidden(sK2(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ spl5_5 ),
    inference(superposition,[],[f55,f98])).

fof(f98,plain,
    ( k1_funct_1(k7_relat_1(sK1,sK0),sK2(k7_relat_1(sK1,sK0))) = k1_funct_1(sK1,sK3(k7_relat_1(sK1,sK0)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k7_relat_1(sK1,X1),X0) = k1_funct_1(sK1,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1))) ) ),
    inference(subsumption_resolution,[],[f54,f31])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1)))
      | k1_funct_1(k7_relat_1(sK1,X1),X0) = k1_funct_1(sK1,X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f32,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

fof(f107,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | spl5_4 ),
    inference(subsumption_resolution,[],[f105,f59])).

fof(f105,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl5_2
    | spl5_4 ),
    inference(subsumption_resolution,[],[f104,f63])).

fof(f104,plain,
    ( ~ v1_funct_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl5_4 ),
    inference(subsumption_resolution,[],[f101,f34])).

fof(f101,plain,
    ( v2_funct_1(k7_relat_1(sK1,sK0))
    | ~ v1_funct_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl5_4 ),
    inference(resolution,[],[f94,f40])).

fof(f94,plain,
    ( ~ r2_hidden(sK3(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0)))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl5_4
  <=> r2_hidden(sK3(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f100,plain,
    ( ~ spl5_4
    | spl5_5
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f88,f66,f96,f92])).

fof(f66,plain,
    ( spl5_3
  <=> k1_funct_1(k7_relat_1(sK1,sK0),sK2(k7_relat_1(sK1,sK0))) = k1_funct_1(k7_relat_1(sK1,sK0),sK3(k7_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f88,plain,
    ( k1_funct_1(k7_relat_1(sK1,sK0),sK2(k7_relat_1(sK1,sK0))) = k1_funct_1(sK1,sK3(k7_relat_1(sK1,sK0)))
    | ~ r2_hidden(sK3(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ spl5_3 ),
    inference(superposition,[],[f55,f68])).

fof(f68,plain,
    ( k1_funct_1(k7_relat_1(sK1,sK0),sK2(k7_relat_1(sK1,sK0))) = k1_funct_1(k7_relat_1(sK1,sK0),sK3(k7_relat_1(sK1,sK0)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f80,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | spl5_2 ),
    inference(subsumption_resolution,[],[f78,f31])).

fof(f78,plain,
    ( ~ v1_relat_1(sK1)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f77,f32])).

fof(f77,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl5_2 ),
    inference(resolution,[],[f64,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f64,plain,
    ( ~ v1_funct_1(k7_relat_1(sK1,sK0))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f76,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f75])).

fof(f75,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f74,f31])).

fof(f74,plain,
    ( ~ v1_relat_1(sK1)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f71,f32])).

fof(f71,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl5_1 ),
    inference(resolution,[],[f60,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f60,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f69,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f56,f66,f62,f58])).

fof(f56,plain,
    ( k1_funct_1(k7_relat_1(sK1,sK0),sK2(k7_relat_1(sK1,sK0))) = k1_funct_1(k7_relat_1(sK1,sK0),sK3(k7_relat_1(sK1,sK0)))
    | ~ v1_funct_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f34,f41])).

fof(f41,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

%------------------------------------------------------------------------------
