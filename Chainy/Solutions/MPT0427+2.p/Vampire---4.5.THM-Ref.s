%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0427+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:29 EST 2020

% Result     : Theorem 5.46s
% Output     : Refutation 6.11s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 198 expanded)
%              Number of leaves         :   25 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  313 ( 711 expanded)
%              Number of equality atoms :   61 (  95 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6390,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1891,f2885,f3665,f3699,f5410,f6266,f6374])).

fof(f6374,plain,
    ( ~ spl29_4
    | ~ spl29_6
    | ~ spl29_11 ),
    inference(avatar_contradiction_clause,[],[f6373])).

fof(f6373,plain,
    ( $false
    | ~ spl29_4
    | ~ spl29_6
    | ~ spl29_11 ),
    inference(subsumption_resolution,[],[f6302,f3225])).

fof(f3225,plain,
    ( r2_hidden(k1_setfam_1(sK6),k1_zfmisc_1(k1_setfam_1(sK5)))
    | ~ spl29_4 ),
    inference(resolution,[],[f1890,f924])).

fof(f924,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f827])).

fof(f827,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f736])).

fof(f736,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK16(X0,X1),X0)
            | ~ r2_hidden(sK16(X0,X1),X1) )
          & ( r1_tarski(sK16(X0,X1),X0)
            | r2_hidden(sK16(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f734,f735])).

fof(f735,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK16(X0,X1),X0)
          | ~ r2_hidden(sK16(X0,X1),X1) )
        & ( r1_tarski(sK16(X0,X1),X0)
          | r2_hidden(sK16(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f734,plain,(
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
    inference(rectify,[],[f733])).

fof(f733,plain,(
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
    inference(nnf_transformation,[],[f285])).

fof(f285,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f1890,plain,
    ( r1_tarski(k1_setfam_1(sK6),k1_setfam_1(sK5))
    | ~ spl29_4 ),
    inference(avatar_component_clause,[],[f1889])).

fof(f1889,plain,
    ( spl29_4
  <=> r1_tarski(k1_setfam_1(sK6),k1_setfam_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_4])])).

fof(f6302,plain,
    ( ~ r2_hidden(k1_setfam_1(sK6),k1_zfmisc_1(k1_setfam_1(sK5)))
    | ~ spl29_6
    | ~ spl29_11 ),
    inference(backward_demodulation,[],[f3714,f6265])).

fof(f6265,plain,
    ( k8_setfam_1(sK4,sK6) = k1_setfam_1(sK6)
    | ~ spl29_11 ),
    inference(avatar_component_clause,[],[f6264])).

fof(f6264,plain,
    ( spl29_11
  <=> k8_setfam_1(sK4,sK6) = k1_setfam_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_11])])).

fof(f3714,plain,
    ( ~ r2_hidden(k8_setfam_1(sK4,sK6),k1_zfmisc_1(k1_setfam_1(sK5)))
    | ~ spl29_6 ),
    inference(backward_demodulation,[],[f1084,f3698])).

fof(f3698,plain,
    ( k8_setfam_1(sK4,sK5) = k1_setfam_1(sK5)
    | ~ spl29_6 ),
    inference(avatar_component_clause,[],[f3697])).

fof(f3697,plain,
    ( spl29_6
  <=> k8_setfam_1(sK4,sK5) = k1_setfam_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_6])])).

fof(f1084,plain,(
    ~ r2_hidden(k8_setfam_1(sK4,sK6),k1_zfmisc_1(k8_setfam_1(sK4,sK5))) ),
    inference(resolution,[],[f782,f925])).

fof(f925,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f826])).

fof(f826,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f736])).

fof(f782,plain,(
    ~ r1_tarski(k8_setfam_1(sK4,sK6),k8_setfam_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f703])).

fof(f703,plain,
    ( ~ r1_tarski(k8_setfam_1(sK4,sK6),k8_setfam_1(sK4,sK5))
    & r1_tarski(sK5,sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4)))
    & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f625,f702,f701])).

fof(f701,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(sK4,X2),k8_setfam_1(sK4,sK5))
          & r1_tarski(sK5,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK4))) )
      & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f702,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k8_setfam_1(sK4,X2),k8_setfam_1(sK4,sK5))
        & r1_tarski(sK5,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK4))) )
   => ( ~ r1_tarski(k8_setfam_1(sK4,sK6),k8_setfam_1(sK4,sK5))
      & r1_tarski(sK5,sK6)
      & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f625,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f624])).

fof(f624,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f616])).

fof(f616,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f615])).

fof(f615,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f6266,plain,
    ( spl29_9
    | spl29_11 ),
    inference(avatar_split_clause,[],[f1073,f6264,f3974])).

fof(f3974,plain,
    ( spl29_9
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_9])])).

fof(f1073,plain,
    ( k8_setfam_1(sK4,sK6) = k1_setfam_1(sK6)
    | k1_xboole_0 = sK6 ),
    inference(backward_demodulation,[],[f1034,f1043])).

fof(f1043,plain,(
    k1_setfam_1(sK6) = k6_setfam_1(sK4,sK6) ),
    inference(resolution,[],[f780,f847])).

fof(f847,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f663])).

fof(f663,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f570])).

fof(f570,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f780,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(sK4))) ),
    inference(cnf_transformation,[],[f703])).

fof(f1034,plain,
    ( k8_setfam_1(sK4,sK6) = k6_setfam_1(sK4,sK6)
    | k1_xboole_0 = sK6 ),
    inference(resolution,[],[f780,f786])).

fof(f786,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f628])).

fof(f628,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f546])).

fof(f546,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f5410,plain,
    ( ~ spl29_5
    | ~ spl29_9 ),
    inference(avatar_contradiction_clause,[],[f5409])).

fof(f5409,plain,
    ( $false
    | ~ spl29_5
    | ~ spl29_9 ),
    inference(subsumption_resolution,[],[f4618,f869])).

fof(f869,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f407])).

fof(f407,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f4618,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_tarski(sK18(sK5)),k1_xboole_0)
    | ~ spl29_5
    | ~ spl29_9 ),
    inference(backward_demodulation,[],[f3888,f3975])).

fof(f3975,plain,
    ( k1_xboole_0 = sK6
    | ~ spl29_9 ),
    inference(avatar_component_clause,[],[f3974])).

fof(f3888,plain,
    ( sK6 = k2_xboole_0(k1_tarski(sK18(sK5)),sK6)
    | ~ spl29_5 ),
    inference(resolution,[],[f3792,f895])).

fof(f895,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f680])).

fof(f680,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f304])).

fof(f304,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f3792,plain,
    ( r2_hidden(sK18(sK5),sK6)
    | ~ spl29_5 ),
    inference(resolution,[],[f3679,f953])).

fof(f953,plain,(
    ! [X16] :
      ( ~ r2_hidden(X16,sK5)
      | r2_hidden(X16,sK6) ) ),
    inference(resolution,[],[f781,f798])).

fof(f798,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f713])).

fof(f713,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f711,f712])).

fof(f712,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f711,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f710])).

fof(f710,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f641])).

fof(f641,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f781,plain,(
    r1_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f703])).

fof(f3679,plain,
    ( r2_hidden(sK18(sK5),sK5)
    | ~ spl29_5 ),
    inference(resolution,[],[f3664,f841])).

fof(f841,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK18(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f744])).

fof(f744,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK18(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK18(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f659,f743])).

fof(f743,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK18(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK18(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f659,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f433])).

fof(f433,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(f3664,plain,
    ( r2_hidden(sK22(k1_zfmisc_1(sK4),sK5),sK5)
    | ~ spl29_5 ),
    inference(avatar_component_clause,[],[f3663])).

fof(f3663,plain,
    ( spl29_5
  <=> r2_hidden(sK22(k1_zfmisc_1(sK4),sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_5])])).

fof(f3699,plain,
    ( spl29_3
    | spl29_6 ),
    inference(avatar_split_clause,[],[f1030,f3697,f1886])).

fof(f1886,plain,
    ( spl29_3
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_3])])).

fof(f1030,plain,
    ( k8_setfam_1(sK4,sK5) = k1_setfam_1(sK5)
    | k1_xboole_0 = sK5 ),
    inference(backward_demodulation,[],[f991,f1000])).

fof(f1000,plain,(
    k1_setfam_1(sK5) = k6_setfam_1(sK4,sK5) ),
    inference(resolution,[],[f779,f847])).

fof(f779,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK4))) ),
    inference(cnf_transformation,[],[f703])).

fof(f991,plain,
    ( k8_setfam_1(sK4,sK5) = k6_setfam_1(sK4,sK5)
    | k1_xboole_0 = sK5 ),
    inference(resolution,[],[f779,f786])).

fof(f3665,plain,
    ( spl29_3
    | spl29_5 ),
    inference(avatar_split_clause,[],[f1023,f3663,f1886])).

fof(f1023,plain,
    ( r2_hidden(sK22(k1_zfmisc_1(sK4),sK5),sK5)
    | k1_xboole_0 = sK5 ),
    inference(resolution,[],[f779,f867])).

fof(f867,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK22(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f759])).

fof(f759,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(sK22(X0,X1),X1)
        & m1_subset_1(sK22(X0,X1),X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22])],[f670,f758])).

fof(f758,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( r2_hidden(sK22(X0,X1),X1)
        & m1_subset_1(sK22(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f670,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f669])).

fof(f669,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f497])).

fof(f497,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

fof(f2885,plain,(
    ~ spl29_3 ),
    inference(avatar_contradiction_clause,[],[f2884])).

fof(f2884,plain,
    ( $false
    | ~ spl29_3 ),
    inference(subsumption_resolution,[],[f2883,f873])).

fof(f873,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f2883,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK4)))
    | ~ spl29_3 ),
    inference(subsumption_resolution,[],[f2880,f1502])).

fof(f1502,plain,(
    r1_tarski(k8_setfam_1(sK4,sK6),sK4) ),
    inference(resolution,[],[f1035,f807])).

fof(f807,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f716])).

fof(f716,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f597])).

fof(f597,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1035,plain,(
    m1_subset_1(k8_setfam_1(sK4,sK6),k1_zfmisc_1(sK4)) ),
    inference(resolution,[],[f780,f788])).

fof(f788,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f629])).

fof(f629,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f561])).

fof(f561,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f2880,plain,
    ( ~ r1_tarski(k8_setfam_1(sK4,sK6),sK4)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK4)))
    | ~ spl29_3 ),
    inference(superposition,[],[f1894,f921])).

fof(f921,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f787])).

fof(f787,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f628])).

fof(f1894,plain,
    ( ~ r1_tarski(k8_setfam_1(sK4,sK6),k8_setfam_1(sK4,k1_xboole_0))
    | ~ spl29_3 ),
    inference(backward_demodulation,[],[f782,f1887])).

fof(f1887,plain,
    ( k1_xboole_0 = sK5
    | ~ spl29_3 ),
    inference(avatar_component_clause,[],[f1886])).

fof(f1891,plain,
    ( spl29_3
    | spl29_4 ),
    inference(avatar_split_clause,[],[f960,f1889,f1886])).

fof(f960,plain,
    ( r1_tarski(k1_setfam_1(sK6),k1_setfam_1(sK5))
    | k1_xboole_0 = sK5 ),
    inference(resolution,[],[f781,f902])).

fof(f902,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f690])).

fof(f690,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f689])).

fof(f689,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f620])).

fof(f620,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).
%------------------------------------------------------------------------------
