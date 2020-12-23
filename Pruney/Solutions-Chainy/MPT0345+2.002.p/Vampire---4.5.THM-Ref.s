%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 484 expanded)
%              Number of leaves         :   19 ( 152 expanded)
%              Depth                    :   14
%              Number of atoms          :  477 (3497 expanded)
%              Number of equality atoms :   50 ( 357 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f487,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f203,f212,f213,f426,f456,f486])).

fof(f486,plain,
    ( spl8_1
    | ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f485])).

fof(f485,plain,
    ( $false
    | spl8_1
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f483,f484])).

fof(f484,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f466,f49])).

fof(f49,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f466,plain,
    ( r2_hidden(sK7(sK2,sK3,sK1),sK0)
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f120,f210,f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f210,plain,
    ( r2_hidden(sK7(sK2,sK3,sK1),sK3)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl8_3
  <=> r2_hidden(sK7(sK2,sK3,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f120,plain,(
    r1_tarski(sK3,sK0) ),
    inference(unit_resulting_resolution,[],[f100,f78])).

fof(f78,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK6(X0,X1),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r1_tarski(sK6(X0,X1),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK6(X0,X1),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( r1_tarski(sK6(X0,X1),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f100,plain,(
    r2_hidden(sK3,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f48,f43,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( sK1 != k4_subset_1(sK0,sK2,sK3)
    & ! [X4] :
        ( ( ( r2_hidden(X4,sK1)
            | ( ~ r2_hidden(X4,sK3)
              & ~ r2_hidden(X4,sK2) ) )
          & ( r2_hidden(X4,sK3)
            | r2_hidden(X4,sK2)
            | ~ r2_hidden(X4,sK1) ) )
        | ~ m1_subset_1(X4,sK0) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f21,f20,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( k4_subset_1(X0,X2,X3) != X1
                & ! [X4] :
                    ( ( ( r2_hidden(X4,X1)
                        | ( ~ r2_hidden(X4,X3)
                          & ~ r2_hidden(X4,X2) ) )
                      & ( r2_hidden(X4,X3)
                        | r2_hidden(X4,X2)
                        | ~ r2_hidden(X4,X1) ) )
                    | ~ m1_subset_1(X4,X0) )
                & m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( sK1 != k4_subset_1(sK0,X2,X3)
              & ! [X4] :
                  ( ( ( r2_hidden(X4,sK1)
                      | ( ~ r2_hidden(X4,X3)
                        & ~ r2_hidden(X4,X2) ) )
                    & ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2)
                      | ~ r2_hidden(X4,sK1) ) )
                  | ~ m1_subset_1(X4,sK0) )
              & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( sK1 != k4_subset_1(sK0,X2,X3)
            & ! [X4] :
                ( ( ( r2_hidden(X4,sK1)
                    | ( ~ r2_hidden(X4,X3)
                      & ~ r2_hidden(X4,X2) ) )
                  & ( r2_hidden(X4,X3)
                    | r2_hidden(X4,X2)
                    | ~ r2_hidden(X4,sK1) ) )
                | ~ m1_subset_1(X4,sK0) )
            & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ? [X3] :
          ( sK1 != k4_subset_1(sK0,sK2,X3)
          & ! [X4] :
              ( ( ( r2_hidden(X4,sK1)
                  | ( ~ r2_hidden(X4,X3)
                    & ~ r2_hidden(X4,sK2) ) )
                & ( r2_hidden(X4,X3)
                  | r2_hidden(X4,sK2)
                  | ~ r2_hidden(X4,sK1) ) )
              | ~ m1_subset_1(X4,sK0) )
          & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X3] :
        ( sK1 != k4_subset_1(sK0,sK2,X3)
        & ! [X4] :
            ( ( ( r2_hidden(X4,sK1)
                | ( ~ r2_hidden(X4,X3)
                  & ~ r2_hidden(X4,sK2) ) )
              & ( r2_hidden(X4,X3)
                | r2_hidden(X4,sK2)
                | ~ r2_hidden(X4,sK1) ) )
            | ~ m1_subset_1(X4,sK0) )
        & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
   => ( sK1 != k4_subset_1(sK0,sK2,sK3)
      & ! [X4] :
          ( ( ( r2_hidden(X4,sK1)
              | ( ~ r2_hidden(X4,sK3)
                & ~ r2_hidden(X4,sK2) ) )
            & ( r2_hidden(X4,sK3)
              | r2_hidden(X4,sK2)
              | ~ r2_hidden(X4,sK1) ) )
          | ~ m1_subset_1(X4,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k4_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( ( r2_hidden(X4,X1)
                      | ( ~ r2_hidden(X4,X3)
                        & ~ r2_hidden(X4,X2) ) )
                    & ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2)
                      | ~ r2_hidden(X4,X1) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k4_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( ( r2_hidden(X4,X1)
                      | ( ~ r2_hidden(X4,X3)
                        & ~ r2_hidden(X4,X2) ) )
                    & ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2)
                      | ~ r2_hidden(X4,X1) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k4_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k4_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,X1)
                      <=> ( r2_hidden(X4,X3)
                          | r2_hidden(X4,X2) ) ) )
                 => k4_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(X0))
             => ( ! [X4] :
                    ( m1_subset_1(X4,X0)
                   => ( r2_hidden(X4,X1)
                    <=> ( r2_hidden(X4,X3)
                        | r2_hidden(X4,X2) ) ) )
               => k4_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_subset_1)).

fof(f48,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f483,plain,
    ( v1_xboole_0(sK0)
    | spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f462,f466,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f462,plain,
    ( ~ m1_subset_1(sK7(sK2,sK3,sK1),sK0)
    | spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f198,f210,f46])).

fof(f46,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | ~ r2_hidden(X4,sK3)
      | r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f198,plain,
    ( ~ r2_hidden(sK7(sK2,sK3,sK1),sK1)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl8_1
  <=> r2_hidden(sK7(sK2,sK3,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f456,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f455])).

fof(f455,plain,
    ( $false
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f453,f454])).

fof(f454,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f436,f49])).

fof(f436,plain,
    ( r2_hidden(sK7(sK2,sK3,sK1),sK0)
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f113,f201,f56])).

fof(f201,plain,
    ( r2_hidden(sK7(sK2,sK3,sK1),sK2)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl8_2
  <=> r2_hidden(sK7(sK2,sK3,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f113,plain,(
    r1_tarski(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f91,f78])).

fof(f91,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f48,f42,f52])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f453,plain,
    ( v1_xboole_0(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f432,f436,f53])).

fof(f432,plain,
    ( ~ m1_subset_1(sK7(sK2,sK3,sK1),sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f198,f201,f45])).

fof(f45,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | ~ r2_hidden(X4,sK2)
      | r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f426,plain,
    ( ~ spl8_1
    | spl8_2
    | spl8_3 ),
    inference(avatar_contradiction_clause,[],[f425])).

fof(f425,plain,
    ( $false
    | ~ spl8_1
    | spl8_2
    | spl8_3 ),
    inference(subsumption_resolution,[],[f424,f423])).

fof(f423,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f228,f49])).

fof(f228,plain,
    ( r2_hidden(sK7(sK2,sK3,sK1),sK0)
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f106,f197,f56])).

fof(f197,plain,
    ( r2_hidden(sK7(sK2,sK3,sK1),sK1)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f196])).

fof(f106,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f84,f78])).

fof(f84,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f48,f41,f52])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f424,plain,
    ( v1_xboole_0(sK0)
    | ~ spl8_1
    | spl8_2
    | spl8_3 ),
    inference(unit_resulting_resolution,[],[f228,f236,f53])).

fof(f236,plain,
    ( ~ m1_subset_1(sK7(sK2,sK3,sK1),sK0)
    | ~ spl8_1
    | spl8_2
    | spl8_3 ),
    inference(unit_resulting_resolution,[],[f197,f202,f209,f44])).

fof(f44,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | r2_hidden(X4,sK2)
      | ~ r2_hidden(X4,sK1)
      | r2_hidden(X4,sK3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f209,plain,
    ( ~ r2_hidden(sK7(sK2,sK3,sK1),sK3)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f208])).

fof(f202,plain,
    ( ~ r2_hidden(sK7(sK2,sK3,sK1),sK2)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f200])).

fof(f213,plain,
    ( ~ spl8_1
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f204,f208,f196])).

fof(f204,plain,
    ( ~ r2_hidden(sK7(sK2,sK3,sK1),sK3)
    | ~ r2_hidden(sK7(sK2,sK3,sK1),sK1) ),
    inference(equality_resolution,[],[f130])).

fof(f130,plain,(
    ! [X2] :
      ( sK1 != X2
      | ~ r2_hidden(sK7(sK2,sK3,X2),sK3)
      | ~ r2_hidden(sK7(sK2,sK3,X2),X2) ) ),
    inference(superposition,[],[f105,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X0,X1)) = X2
      | ~ r2_hidden(sK7(X0,X1,X2),X1)
      | ~ r2_hidden(sK7(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f69,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK7(X0,X1,X2),X1)
      | ~ r2_hidden(sK7(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
              & ~ r2_hidden(sK7(X0,X1,X2),X0) )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( r2_hidden(sK7(X0,X1,X2),X1)
            | r2_hidden(sK7(X0,X1,X2),X0)
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
            & ~ r2_hidden(sK7(X0,X1,X2),X0) )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( r2_hidden(sK7(X0,X1,X2),X1)
          | r2_hidden(sK7(X0,X1,X2),X0)
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f105,plain,(
    sK1 != k3_tarski(k2_tarski(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f104,f42])).

fof(f104,plain,
    ( sK1 != k3_tarski(k2_tarski(sK2,sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f103,f43])).

fof(f103,plain,
    ( sK1 != k3_tarski(k2_tarski(sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f47,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f63,f51])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f47,plain,(
    sK1 != k4_subset_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f212,plain,
    ( spl8_1
    | spl8_2
    | spl8_3 ),
    inference(avatar_split_clause,[],[f205,f208,f200,f196])).

fof(f205,plain,
    ( r2_hidden(sK7(sK2,sK3,sK1),sK3)
    | r2_hidden(sK7(sK2,sK3,sK1),sK2)
    | r2_hidden(sK7(sK2,sK3,sK1),sK1) ),
    inference(equality_resolution,[],[f128])).

fof(f128,plain,(
    ! [X0] :
      ( sK1 != X0
      | r2_hidden(sK7(sK2,sK3,X0),sK3)
      | r2_hidden(sK7(sK2,sK3,X0),sK2)
      | r2_hidden(sK7(sK2,sK3,X0),X0) ) ),
    inference(superposition,[],[f105,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X0,X1)) = X2
      | r2_hidden(sK7(X0,X1,X2),X1)
      | r2_hidden(sK7(X0,X1,X2),X0)
      | r2_hidden(sK7(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f67,f51])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK7(X0,X1,X2),X1)
      | r2_hidden(sK7(X0,X1,X2),X0)
      | r2_hidden(sK7(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f203,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f194,f200,f196])).

fof(f194,plain,
    ( ~ r2_hidden(sK7(sK2,sK3,sK1),sK2)
    | ~ r2_hidden(sK7(sK2,sK3,sK1),sK1) ),
    inference(equality_resolution,[],[f129])).

fof(f129,plain,(
    ! [X1] :
      ( sK1 != X1
      | ~ r2_hidden(sK7(sK2,sK3,X1),sK2)
      | ~ r2_hidden(sK7(sK2,sK3,X1),X1) ) ),
    inference(superposition,[],[f105,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X0,X1)) = X2
      | ~ r2_hidden(sK7(X0,X1,X2),X0)
      | ~ r2_hidden(sK7(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f68,f51])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK7(X0,X1,X2),X0)
      | ~ r2_hidden(sK7(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:15:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (18217)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (18202)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (18225)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (18220)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (18211)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (18228)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.56  % (18206)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.57  % (18223)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.57  % (18215)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.58  % (18231)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.59  % (18229)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.60  % (18203)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.60  % (18201)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.60  % (18207)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.61  % (18204)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.61  % (18221)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.61  % (18219)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.61  % (18213)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.61  % (18228)Refutation found. Thanks to Tanya!
% 0.20/0.61  % SZS status Theorem for theBenchmark
% 0.20/0.61  % SZS output start Proof for theBenchmark
% 0.20/0.61  fof(f487,plain,(
% 0.20/0.61    $false),
% 0.20/0.61    inference(avatar_sat_refutation,[],[f203,f212,f213,f426,f456,f486])).
% 0.20/0.61  fof(f486,plain,(
% 0.20/0.61    spl8_1 | ~spl8_3),
% 0.20/0.61    inference(avatar_contradiction_clause,[],[f485])).
% 0.20/0.61  fof(f485,plain,(
% 0.20/0.61    $false | (spl8_1 | ~spl8_3)),
% 0.20/0.61    inference(subsumption_resolution,[],[f483,f484])).
% 0.20/0.61  fof(f484,plain,(
% 0.20/0.61    ~v1_xboole_0(sK0) | ~spl8_3),
% 0.20/0.61    inference(unit_resulting_resolution,[],[f466,f49])).
% 0.20/0.61  fof(f49,plain,(
% 0.20/0.61    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.61    inference(cnf_transformation,[],[f26])).
% 0.20/0.61  fof(f26,plain,(
% 0.20/0.61    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 0.20/0.61  fof(f25,plain,(
% 0.20/0.61    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.20/0.61    introduced(choice_axiom,[])).
% 0.20/0.61  fof(f24,plain,(
% 0.20/0.61    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.61    inference(rectify,[],[f23])).
% 0.20/0.61  fof(f23,plain,(
% 0.20/0.61    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.61    inference(nnf_transformation,[],[f1])).
% 0.20/0.61  fof(f1,axiom,(
% 0.20/0.61    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.61  fof(f466,plain,(
% 0.20/0.61    r2_hidden(sK7(sK2,sK3,sK1),sK0) | ~spl8_3),
% 0.20/0.61    inference(unit_resulting_resolution,[],[f120,f210,f56])).
% 0.20/0.61  fof(f56,plain,(
% 0.20/0.61    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.61    inference(cnf_transformation,[],[f31])).
% 0.20/0.61  fof(f31,plain,(
% 0.20/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).
% 0.20/0.61  fof(f30,plain,(
% 0.20/0.61    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.20/0.61    introduced(choice_axiom,[])).
% 0.20/0.61  fof(f29,plain,(
% 0.20/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.61    inference(rectify,[],[f28])).
% 0.20/0.61  fof(f28,plain,(
% 0.20/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.61    inference(nnf_transformation,[],[f14])).
% 0.20/0.61  fof(f14,plain,(
% 0.20/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.61    inference(ennf_transformation,[],[f2])).
% 0.20/0.61  fof(f2,axiom,(
% 0.20/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.61  fof(f210,plain,(
% 0.20/0.61    r2_hidden(sK7(sK2,sK3,sK1),sK3) | ~spl8_3),
% 0.20/0.61    inference(avatar_component_clause,[],[f208])).
% 0.20/0.61  fof(f208,plain,(
% 0.20/0.61    spl8_3 <=> r2_hidden(sK7(sK2,sK3,sK1),sK3)),
% 0.20/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.61  fof(f120,plain,(
% 0.20/0.61    r1_tarski(sK3,sK0)),
% 0.20/0.61    inference(unit_resulting_resolution,[],[f100,f78])).
% 0.20/0.61  fof(f78,plain,(
% 0.20/0.61    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.20/0.61    inference(equality_resolution,[],[f59])).
% 0.20/0.61  fof(f59,plain,(
% 0.20/0.61    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.61    inference(cnf_transformation,[],[f35])).
% 0.20/0.61  fof(f35,plain,(
% 0.20/0.61    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK6(X0,X1),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r1_tarski(sK6(X0,X1),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f33,f34])).
% 0.20/0.61  fof(f34,plain,(
% 0.20/0.61    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK6(X0,X1),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r1_tarski(sK6(X0,X1),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 0.20/0.61    introduced(choice_axiom,[])).
% 0.20/0.61  fof(f33,plain,(
% 0.20/0.61    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.61    inference(rectify,[],[f32])).
% 0.20/0.61  fof(f32,plain,(
% 0.20/0.61    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.61    inference(nnf_transformation,[],[f4])).
% 0.20/0.61  fof(f4,axiom,(
% 0.20/0.61    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.61  fof(f100,plain,(
% 0.20/0.61    r2_hidden(sK3,k1_zfmisc_1(sK0))),
% 0.20/0.61    inference(unit_resulting_resolution,[],[f48,f43,f52])).
% 0.20/0.61  fof(f52,plain,(
% 0.20/0.61    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.61    inference(cnf_transformation,[],[f27])).
% 0.20/0.61  fof(f27,plain,(
% 0.20/0.61    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.20/0.61    inference(nnf_transformation,[],[f13])).
% 0.20/0.61  fof(f13,plain,(
% 0.20/0.61    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.61    inference(ennf_transformation,[],[f6])).
% 0.20/0.61  fof(f6,axiom,(
% 0.20/0.61    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.61  fof(f43,plain,(
% 0.20/0.61    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.20/0.61    inference(cnf_transformation,[],[f22])).
% 0.20/0.61  fof(f22,plain,(
% 0.20/0.61    ((sK1 != k4_subset_1(sK0,sK2,sK3) & ! [X4] : (((r2_hidden(X4,sK1) | (~r2_hidden(X4,sK3) & ~r2_hidden(X4,sK2))) & (r2_hidden(X4,sK3) | r2_hidden(X4,sK2) | ~r2_hidden(X4,sK1))) | ~m1_subset_1(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f21,f20,f19])).
% 0.20/0.61  fof(f19,plain,(
% 0.20/0.61    ? [X0,X1] : (? [X2] : (? [X3] : (k4_subset_1(X0,X2,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | (~r2_hidden(X4,X3) & ~r2_hidden(X4,X2))) & (r2_hidden(X4,X3) | r2_hidden(X4,X2) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (? [X3] : (sK1 != k4_subset_1(sK0,X2,X3) & ! [X4] : (((r2_hidden(X4,sK1) | (~r2_hidden(X4,X3) & ~r2_hidden(X4,X2))) & (r2_hidden(X4,X3) | r2_hidden(X4,X2) | ~r2_hidden(X4,sK1))) | ~m1_subset_1(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.61    introduced(choice_axiom,[])).
% 0.20/0.61  fof(f20,plain,(
% 0.20/0.61    ? [X2] : (? [X3] : (sK1 != k4_subset_1(sK0,X2,X3) & ! [X4] : (((r2_hidden(X4,sK1) | (~r2_hidden(X4,X3) & ~r2_hidden(X4,X2))) & (r2_hidden(X4,X3) | r2_hidden(X4,X2) | ~r2_hidden(X4,sK1))) | ~m1_subset_1(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (? [X3] : (sK1 != k4_subset_1(sK0,sK2,X3) & ! [X4] : (((r2_hidden(X4,sK1) | (~r2_hidden(X4,X3) & ~r2_hidden(X4,sK2))) & (r2_hidden(X4,X3) | r2_hidden(X4,sK2) | ~r2_hidden(X4,sK1))) | ~m1_subset_1(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.20/0.61    introduced(choice_axiom,[])).
% 0.20/0.61  fof(f21,plain,(
% 0.20/0.61    ? [X3] : (sK1 != k4_subset_1(sK0,sK2,X3) & ! [X4] : (((r2_hidden(X4,sK1) | (~r2_hidden(X4,X3) & ~r2_hidden(X4,sK2))) & (r2_hidden(X4,X3) | r2_hidden(X4,sK2) | ~r2_hidden(X4,sK1))) | ~m1_subset_1(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(sK0))) => (sK1 != k4_subset_1(sK0,sK2,sK3) & ! [X4] : (((r2_hidden(X4,sK1) | (~r2_hidden(X4,sK3) & ~r2_hidden(X4,sK2))) & (r2_hidden(X4,sK3) | r2_hidden(X4,sK2) | ~r2_hidden(X4,sK1))) | ~m1_subset_1(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(sK0)))),
% 0.20/0.61    introduced(choice_axiom,[])).
% 0.20/0.61  fof(f18,plain,(
% 0.20/0.61    ? [X0,X1] : (? [X2] : (? [X3] : (k4_subset_1(X0,X2,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | (~r2_hidden(X4,X3) & ~r2_hidden(X4,X2))) & (r2_hidden(X4,X3) | r2_hidden(X4,X2) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.61    inference(flattening,[],[f17])).
% 0.20/0.61  fof(f17,plain,(
% 0.20/0.61    ? [X0,X1] : (? [X2] : (? [X3] : (k4_subset_1(X0,X2,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | (~r2_hidden(X4,X3) & ~r2_hidden(X4,X2))) & ((r2_hidden(X4,X3) | r2_hidden(X4,X2)) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.61    inference(nnf_transformation,[],[f12])).
% 0.20/0.61  fof(f12,plain,(
% 0.20/0.61    ? [X0,X1] : (? [X2] : (? [X3] : (k4_subset_1(X0,X2,X3) != X1 & ! [X4] : ((r2_hidden(X4,X1) <=> (r2_hidden(X4,X3) | r2_hidden(X4,X2))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.61    inference(flattening,[],[f11])).
% 0.20/0.61  fof(f11,plain,(
% 0.20/0.61    ? [X0,X1] : (? [X2] : (? [X3] : ((k4_subset_1(X0,X2,X3) != X1 & ! [X4] : ((r2_hidden(X4,X1) <=> (r2_hidden(X4,X3) | r2_hidden(X4,X2))) | ~m1_subset_1(X4,X0))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.61    inference(ennf_transformation,[],[f10])).
% 0.20/0.61  fof(f10,negated_conjecture,(
% 0.20/0.61    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,X1) <=> (r2_hidden(X4,X3) | r2_hidden(X4,X2)))) => k4_subset_1(X0,X2,X3) = X1))))),
% 0.20/0.61    inference(negated_conjecture,[],[f9])).
% 0.20/0.61  fof(f9,conjecture,(
% 0.20/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,X1) <=> (r2_hidden(X4,X3) | r2_hidden(X4,X2)))) => k4_subset_1(X0,X2,X3) = X1))))),
% 0.20/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_subset_1)).
% 0.20/0.61  fof(f48,plain,(
% 0.20/0.61    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.20/0.61    inference(cnf_transformation,[],[f7])).
% 0.20/0.61  fof(f7,axiom,(
% 0.20/0.61    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.20/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.20/0.61  fof(f483,plain,(
% 0.20/0.61    v1_xboole_0(sK0) | (spl8_1 | ~spl8_3)),
% 0.20/0.61    inference(unit_resulting_resolution,[],[f462,f466,f53])).
% 0.20/0.61  fof(f53,plain,(
% 0.20/0.61    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.61    inference(cnf_transformation,[],[f27])).
% 0.20/0.61  fof(f462,plain,(
% 0.20/0.61    ~m1_subset_1(sK7(sK2,sK3,sK1),sK0) | (spl8_1 | ~spl8_3)),
% 0.20/0.61    inference(unit_resulting_resolution,[],[f198,f210,f46])).
% 0.20/0.61  fof(f46,plain,(
% 0.20/0.61    ( ! [X4] : (~m1_subset_1(X4,sK0) | ~r2_hidden(X4,sK3) | r2_hidden(X4,sK1)) )),
% 0.20/0.61    inference(cnf_transformation,[],[f22])).
% 0.20/0.61  fof(f198,plain,(
% 0.20/0.61    ~r2_hidden(sK7(sK2,sK3,sK1),sK1) | spl8_1),
% 0.20/0.61    inference(avatar_component_clause,[],[f196])).
% 0.20/0.61  fof(f196,plain,(
% 0.20/0.61    spl8_1 <=> r2_hidden(sK7(sK2,sK3,sK1),sK1)),
% 0.20/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.61  fof(f456,plain,(
% 0.20/0.61    spl8_1 | ~spl8_2),
% 0.20/0.61    inference(avatar_contradiction_clause,[],[f455])).
% 0.20/0.61  fof(f455,plain,(
% 0.20/0.61    $false | (spl8_1 | ~spl8_2)),
% 0.20/0.61    inference(subsumption_resolution,[],[f453,f454])).
% 0.20/0.61  fof(f454,plain,(
% 0.20/0.61    ~v1_xboole_0(sK0) | ~spl8_2),
% 0.20/0.61    inference(unit_resulting_resolution,[],[f436,f49])).
% 0.20/0.61  fof(f436,plain,(
% 0.20/0.61    r2_hidden(sK7(sK2,sK3,sK1),sK0) | ~spl8_2),
% 0.20/0.61    inference(unit_resulting_resolution,[],[f113,f201,f56])).
% 0.20/0.61  fof(f201,plain,(
% 0.20/0.61    r2_hidden(sK7(sK2,sK3,sK1),sK2) | ~spl8_2),
% 0.20/0.61    inference(avatar_component_clause,[],[f200])).
% 0.20/0.61  fof(f200,plain,(
% 0.20/0.61    spl8_2 <=> r2_hidden(sK7(sK2,sK3,sK1),sK2)),
% 0.20/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.61  fof(f113,plain,(
% 0.20/0.61    r1_tarski(sK2,sK0)),
% 0.20/0.61    inference(unit_resulting_resolution,[],[f91,f78])).
% 0.20/0.61  fof(f91,plain,(
% 0.20/0.61    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.61    inference(unit_resulting_resolution,[],[f48,f42,f52])).
% 0.20/0.61  fof(f42,plain,(
% 0.20/0.61    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.61    inference(cnf_transformation,[],[f22])).
% 0.20/0.61  fof(f453,plain,(
% 0.20/0.61    v1_xboole_0(sK0) | (spl8_1 | ~spl8_2)),
% 0.20/0.61    inference(unit_resulting_resolution,[],[f432,f436,f53])).
% 0.20/0.61  fof(f432,plain,(
% 0.20/0.61    ~m1_subset_1(sK7(sK2,sK3,sK1),sK0) | (spl8_1 | ~spl8_2)),
% 0.20/0.61    inference(unit_resulting_resolution,[],[f198,f201,f45])).
% 0.20/0.61  fof(f45,plain,(
% 0.20/0.61    ( ! [X4] : (~m1_subset_1(X4,sK0) | ~r2_hidden(X4,sK2) | r2_hidden(X4,sK1)) )),
% 0.20/0.61    inference(cnf_transformation,[],[f22])).
% 0.20/0.61  fof(f426,plain,(
% 0.20/0.61    ~spl8_1 | spl8_2 | spl8_3),
% 0.20/0.61    inference(avatar_contradiction_clause,[],[f425])).
% 0.20/0.61  fof(f425,plain,(
% 0.20/0.61    $false | (~spl8_1 | spl8_2 | spl8_3)),
% 0.20/0.61    inference(subsumption_resolution,[],[f424,f423])).
% 0.20/0.61  fof(f423,plain,(
% 0.20/0.61    ~v1_xboole_0(sK0) | ~spl8_1),
% 0.20/0.61    inference(unit_resulting_resolution,[],[f228,f49])).
% 0.20/0.61  fof(f228,plain,(
% 0.20/0.61    r2_hidden(sK7(sK2,sK3,sK1),sK0) | ~spl8_1),
% 0.20/0.61    inference(unit_resulting_resolution,[],[f106,f197,f56])).
% 0.20/0.61  fof(f197,plain,(
% 0.20/0.61    r2_hidden(sK7(sK2,sK3,sK1),sK1) | ~spl8_1),
% 0.20/0.61    inference(avatar_component_clause,[],[f196])).
% 0.20/0.61  fof(f106,plain,(
% 0.20/0.61    r1_tarski(sK1,sK0)),
% 0.20/0.61    inference(unit_resulting_resolution,[],[f84,f78])).
% 0.20/0.61  fof(f84,plain,(
% 0.20/0.61    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.61    inference(unit_resulting_resolution,[],[f48,f41,f52])).
% 0.20/0.61  fof(f41,plain,(
% 0.20/0.61    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.61    inference(cnf_transformation,[],[f22])).
% 0.20/0.61  fof(f424,plain,(
% 0.20/0.61    v1_xboole_0(sK0) | (~spl8_1 | spl8_2 | spl8_3)),
% 0.20/0.61    inference(unit_resulting_resolution,[],[f228,f236,f53])).
% 0.20/0.61  fof(f236,plain,(
% 0.20/0.61    ~m1_subset_1(sK7(sK2,sK3,sK1),sK0) | (~spl8_1 | spl8_2 | spl8_3)),
% 0.20/0.61    inference(unit_resulting_resolution,[],[f197,f202,f209,f44])).
% 0.20/0.61  fof(f44,plain,(
% 0.20/0.61    ( ! [X4] : (~m1_subset_1(X4,sK0) | r2_hidden(X4,sK2) | ~r2_hidden(X4,sK1) | r2_hidden(X4,sK3)) )),
% 0.20/0.61    inference(cnf_transformation,[],[f22])).
% 0.20/0.61  fof(f209,plain,(
% 0.20/0.61    ~r2_hidden(sK7(sK2,sK3,sK1),sK3) | spl8_3),
% 0.20/0.61    inference(avatar_component_clause,[],[f208])).
% 0.20/0.61  fof(f202,plain,(
% 0.20/0.61    ~r2_hidden(sK7(sK2,sK3,sK1),sK2) | spl8_2),
% 0.20/0.61    inference(avatar_component_clause,[],[f200])).
% 0.20/0.61  fof(f213,plain,(
% 0.20/0.61    ~spl8_1 | ~spl8_3),
% 0.20/0.61    inference(avatar_split_clause,[],[f204,f208,f196])).
% 0.20/0.61  fof(f204,plain,(
% 0.20/0.61    ~r2_hidden(sK7(sK2,sK3,sK1),sK3) | ~r2_hidden(sK7(sK2,sK3,sK1),sK1)),
% 0.20/0.61    inference(equality_resolution,[],[f130])).
% 0.20/0.61  fof(f130,plain,(
% 0.20/0.61    ( ! [X2] : (sK1 != X2 | ~r2_hidden(sK7(sK2,sK3,X2),sK3) | ~r2_hidden(sK7(sK2,sK3,X2),X2)) )),
% 0.20/0.61    inference(superposition,[],[f105,f71])).
% 0.20/0.61  fof(f71,plain,(
% 0.20/0.61    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = X2 | ~r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) )),
% 0.20/0.61    inference(definition_unfolding,[],[f69,f51])).
% 0.20/0.61  fof(f51,plain,(
% 0.20/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.61    inference(cnf_transformation,[],[f5])).
% 0.20/0.61  fof(f5,axiom,(
% 0.20/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.61  fof(f69,plain,(
% 0.20/0.61    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) )),
% 0.20/0.61    inference(cnf_transformation,[],[f40])).
% 0.20/0.61  fof(f40,plain,(
% 0.20/0.61    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK7(X0,X1,X2),X1) & ~r2_hidden(sK7(X0,X1,X2),X0)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (r2_hidden(sK7(X0,X1,X2),X1) | r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f38,f39])).
% 0.20/0.61  fof(f39,plain,(
% 0.20/0.61    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK7(X0,X1,X2),X1) & ~r2_hidden(sK7(X0,X1,X2),X0)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (r2_hidden(sK7(X0,X1,X2),X1) | r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 0.20/0.61    introduced(choice_axiom,[])).
% 0.20/0.61  fof(f38,plain,(
% 0.20/0.61    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.61    inference(rectify,[],[f37])).
% 0.20/0.61  fof(f37,plain,(
% 0.20/0.61    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.61    inference(flattening,[],[f36])).
% 0.20/0.61  fof(f36,plain,(
% 0.20/0.61    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.61    inference(nnf_transformation,[],[f3])).
% 0.20/0.61  fof(f3,axiom,(
% 0.20/0.61    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.20/0.61  fof(f105,plain,(
% 0.20/0.61    sK1 != k3_tarski(k2_tarski(sK2,sK3))),
% 0.20/0.61    inference(subsumption_resolution,[],[f104,f42])).
% 0.20/0.61  fof(f104,plain,(
% 0.20/0.61    sK1 != k3_tarski(k2_tarski(sK2,sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.61    inference(subsumption_resolution,[],[f103,f43])).
% 0.20/0.61  fof(f103,plain,(
% 0.20/0.61    sK1 != k3_tarski(k2_tarski(sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.61    inference(superposition,[],[f47,f70])).
% 0.20/0.61  fof(f70,plain,(
% 0.20/0.61    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.61    inference(definition_unfolding,[],[f63,f51])).
% 0.20/0.61  fof(f63,plain,(
% 0.20/0.61    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.61    inference(cnf_transformation,[],[f16])).
% 0.20/0.61  fof(f16,plain,(
% 0.20/0.61    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.61    inference(flattening,[],[f15])).
% 0.20/0.61  fof(f15,plain,(
% 0.20/0.61    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.61    inference(ennf_transformation,[],[f8])).
% 0.20/0.61  fof(f8,axiom,(
% 0.20/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.20/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.20/0.61  fof(f47,plain,(
% 0.20/0.61    sK1 != k4_subset_1(sK0,sK2,sK3)),
% 0.20/0.61    inference(cnf_transformation,[],[f22])).
% 0.20/0.61  fof(f212,plain,(
% 0.20/0.61    spl8_1 | spl8_2 | spl8_3),
% 0.20/0.61    inference(avatar_split_clause,[],[f205,f208,f200,f196])).
% 0.20/0.61  fof(f205,plain,(
% 0.20/0.61    r2_hidden(sK7(sK2,sK3,sK1),sK3) | r2_hidden(sK7(sK2,sK3,sK1),sK2) | r2_hidden(sK7(sK2,sK3,sK1),sK1)),
% 0.20/0.61    inference(equality_resolution,[],[f128])).
% 0.20/0.61  fof(f128,plain,(
% 0.20/0.61    ( ! [X0] : (sK1 != X0 | r2_hidden(sK7(sK2,sK3,X0),sK3) | r2_hidden(sK7(sK2,sK3,X0),sK2) | r2_hidden(sK7(sK2,sK3,X0),X0)) )),
% 0.20/0.61    inference(superposition,[],[f105,f73])).
% 0.20/0.61  fof(f73,plain,(
% 0.20/0.61    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = X2 | r2_hidden(sK7(X0,X1,X2),X1) | r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2)) )),
% 0.20/0.61    inference(definition_unfolding,[],[f67,f51])).
% 0.20/0.61  fof(f67,plain,(
% 0.20/0.61    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK7(X0,X1,X2),X1) | r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2)) )),
% 0.20/0.61    inference(cnf_transformation,[],[f40])).
% 0.20/0.61  fof(f203,plain,(
% 0.20/0.61    ~spl8_1 | ~spl8_2),
% 0.20/0.61    inference(avatar_split_clause,[],[f194,f200,f196])).
% 0.20/0.61  fof(f194,plain,(
% 0.20/0.61    ~r2_hidden(sK7(sK2,sK3,sK1),sK2) | ~r2_hidden(sK7(sK2,sK3,sK1),sK1)),
% 0.20/0.61    inference(equality_resolution,[],[f129])).
% 0.20/0.61  fof(f129,plain,(
% 0.20/0.61    ( ! [X1] : (sK1 != X1 | ~r2_hidden(sK7(sK2,sK3,X1),sK2) | ~r2_hidden(sK7(sK2,sK3,X1),X1)) )),
% 0.20/0.61    inference(superposition,[],[f105,f72])).
% 0.20/0.61  fof(f72,plain,(
% 0.20/0.61    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = X2 | ~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) )),
% 0.20/0.61    inference(definition_unfolding,[],[f68,f51])).
% 0.20/0.61  fof(f68,plain,(
% 0.20/0.61    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) )),
% 0.20/0.61    inference(cnf_transformation,[],[f40])).
% 0.20/0.61  % SZS output end Proof for theBenchmark
% 0.20/0.61  % (18228)------------------------------
% 0.20/0.61  % (18228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.61  % (18228)Termination reason: Refutation
% 0.20/0.61  
% 0.20/0.61  % (18228)Memory used [KB]: 11129
% 0.20/0.61  % (18228)Time elapsed: 0.209 s
% 0.20/0.61  % (18228)------------------------------
% 0.20/0.61  % (18228)------------------------------
% 0.20/0.62  % (18193)Success in time 0.255 s
%------------------------------------------------------------------------------
