%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : subset_1__t57_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:25 EDT 2019

% Result     : Theorem 3.56s
% Output     : Refutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 171 expanded)
%              Number of leaves         :   17 (  54 expanded)
%              Depth                    :   20
%              Number of atoms          :  365 ( 871 expanded)
%              Number of equality atoms :  116 ( 184 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f134011,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f122,f129,f136,f133924,f134010])).

fof(f134010,plain,(
    ~ spl8_0 ),
    inference(avatar_contradiction_clause,[],[f134009])).

fof(f134009,plain,
    ( $false
    | ~ spl8_0 ),
    inference(subsumption_resolution,[],[f133926,f49])).

fof(f49,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ m1_subset_1(k1_enumset1(sK1,sK2,sK3),k1_zfmisc_1(sK0))
    & k1_xboole_0 != sK0
    & m1_subset_1(sK3,sK0)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0))
                & k1_xboole_0 != X0
                & m1_subset_1(X3,X0) )
            & m1_subset_1(X2,X0) )
        & m1_subset_1(X1,X0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k1_enumset1(sK1,X2,X3),k1_zfmisc_1(sK0))
              & k1_xboole_0 != sK0
              & m1_subset_1(X3,sK0) )
          & m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0))
              & k1_xboole_0 != X0
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
     => ( ? [X3] :
            ( ~ m1_subset_1(k1_enumset1(X1,sK2,X3),k1_zfmisc_1(X0))
            & k1_xboole_0 != X0
            & m1_subset_1(X3,X0) )
        & m1_subset_1(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X3,X0) )
     => ( ~ m1_subset_1(k1_enumset1(X1,X2,sK3),k1_zfmisc_1(X0))
        & k1_xboole_0 != X0
        & m1_subset_1(sK3,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0))
              & k1_xboole_0 != X0
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0))
              & k1_xboole_0 != X0
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ! [X2] :
            ( m1_subset_1(X2,X0)
           => ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( k1_xboole_0 != X0
                 => m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ! [X3] :
              ( m1_subset_1(X3,X0)
             => ( k1_xboole_0 != X0
               => m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t57_subset_1.p',t57_subset_1)).

fof(f133926,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_0 ),
    inference(resolution,[],[f115,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t57_subset_1.p',t6_boole)).

fof(f115,plain,
    ( v1_xboole_0(sK0)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl8_0
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f133924,plain,
    ( ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f133923])).

fof(f133923,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f133922,f121])).

fof(f121,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl8_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f133922,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f133921,f135])).

fof(f135,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl8_6
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f133921,plain,
    ( ~ r2_hidden(sK3,sK0)
    | ~ r2_hidden(sK1,sK0)
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f133863,f128])).

fof(f128,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl8_4
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f133863,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ r2_hidden(sK3,sK0)
    | ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f38423,f149])).

fof(f149,plain,(
    ~ r2_hidden(k1_enumset1(sK1,sK2,sK3),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f148,f50])).

fof(f50,plain,(
    ~ m1_subset_1(k1_enumset1(sK1,sK2,sK3),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f148,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f55,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t57_subset_1.p',t7_boole)).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/subset_1__t57_subset_1.p',d2_subset_1)).

fof(f38423,plain,(
    ! [X21,X19,X20,X18] :
      ( r2_hidden(k1_enumset1(X18,X19,X20),k1_zfmisc_1(X21))
      | ~ r2_hidden(X19,X21)
      | ~ r2_hidden(X20,X21)
      | ~ r2_hidden(X18,X21) ) ),
    inference(subsumption_resolution,[],[f38399,f76])).

fof(f76,plain,(
    ! [X0,X3] :
      ( ~ r1_tarski(X3,X0)
      | r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f38,f39])).

fof(f39,plain,(
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

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t57_subset_1.p',d1_zfmisc_1)).

fof(f38399,plain,(
    ! [X21,X19,X20,X18] :
      ( ~ r2_hidden(X18,X21)
      | r1_tarski(k1_enumset1(X18,X19,X20),X21)
      | ~ r2_hidden(X19,X21)
      | ~ r2_hidden(X20,X21)
      | r2_hidden(k1_enumset1(X18,X19,X20),k1_zfmisc_1(X21)) ) ),
    inference(superposition,[],[f61,f23088])).

fof(f23088,plain,(
    ! [X21,X19,X20,X18] :
      ( sK5(k1_enumset1(X18,X19,X20),X21) = X18
      | ~ r2_hidden(X19,X21)
      | ~ r2_hidden(X20,X21)
      | r2_hidden(k1_enumset1(X18,X19,X20),k1_zfmisc_1(X21)) ) ),
    inference(subsumption_resolution,[],[f23075,f76])).

fof(f23075,plain,(
    ! [X21,X19,X20,X18] :
      ( ~ r2_hidden(X19,X21)
      | r1_tarski(k1_enumset1(X18,X19,X20),X21)
      | sK5(k1_enumset1(X18,X19,X20),X21) = X18
      | ~ r2_hidden(X20,X21)
      | r2_hidden(k1_enumset1(X18,X19,X20),k1_zfmisc_1(X21)) ) ),
    inference(superposition,[],[f61,f9329])).

fof(f9329,plain,(
    ! [X21,X19,X20,X18] :
      ( sK5(k1_enumset1(X18,X19,X20),X21) = X19
      | sK5(k1_enumset1(X18,X19,X20),X21) = X18
      | ~ r2_hidden(X20,X21)
      | r2_hidden(k1_enumset1(X18,X19,X20),k1_zfmisc_1(X21)) ) ),
    inference(subsumption_resolution,[],[f9322,f76])).

fof(f9322,plain,(
    ! [X21,X19,X20,X18] :
      ( ~ r2_hidden(X20,X21)
      | r1_tarski(k1_enumset1(X18,X19,X20),X21)
      | sK5(k1_enumset1(X18,X19,X20),X21) = X18
      | sK5(k1_enumset1(X18,X19,X20),X21) = X19
      | r2_hidden(k1_enumset1(X18,X19,X20),k1_zfmisc_1(X21)) ) ),
    inference(superposition,[],[f61,f363])).

fof(f363,plain,(
    ! [X30,X31,X29,X32] :
      ( sK5(k1_enumset1(X30,X29,X31),X32) = X31
      | sK5(k1_enumset1(X30,X29,X31),X32) = X30
      | sK5(k1_enumset1(X30,X29,X31),X32) = X29
      | r2_hidden(k1_enumset1(X30,X29,X31),k1_zfmisc_1(X32)) ) ),
    inference(resolution,[],[f84,f153])).

fof(f153,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r2_hidden(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f60,f76])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t57_subset_1.p',d3_tarski)).

fof(f84,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k1_enumset1(X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK7(X0,X1,X2,X3) != X2
              & sK7(X0,X1,X2,X3) != X1
              & sK7(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK7(X0,X1,X2,X3),X3) )
          & ( sK7(X0,X1,X2,X3) = X2
            | sK7(X0,X1,X2,X3) = X1
            | sK7(X0,X1,X2,X3) = X0
            | r2_hidden(sK7(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f43,f44])).

fof(f44,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK7(X0,X1,X2,X3) != X2
            & sK7(X0,X1,X2,X3) != X1
            & sK7(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK7(X0,X1,X2,X3),X3) )
        & ( sK7(X0,X1,X2,X3) = X2
          | sK7(X0,X1,X2,X3) = X1
          | sK7(X0,X1,X2,X3) = X0
          | r2_hidden(sK7(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t57_subset_1.p',d1_enumset1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f136,plain,
    ( spl8_0
    | spl8_6 ),
    inference(avatar_split_clause,[],[f107,f134,f114])).

fof(f107,plain,
    ( r2_hidden(sK3,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f54,f48])).

fof(f48,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f129,plain,
    ( spl8_0
    | spl8_4 ),
    inference(avatar_split_clause,[],[f106,f127,f114])).

fof(f106,plain,
    ( r2_hidden(sK2,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f54,f47])).

fof(f47,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f122,plain,
    ( spl8_0
    | spl8_2 ),
    inference(avatar_split_clause,[],[f105,f120,f114])).

fof(f105,plain,
    ( r2_hidden(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f54,f46])).

fof(f46,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
