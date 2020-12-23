%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 183 expanded)
%              Number of leaves         :   21 (  57 expanded)
%              Depth                    :   11
%              Number of atoms          :  367 ( 679 expanded)
%              Number of equality atoms :  142 ( 226 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f176,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f103,f111,f124,f126,f150,f153,f161,f175])).

fof(f175,plain,
    ( ~ spl6_5
    | ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(resolution,[],[f173,f40])).

fof(f40,plain,(
    ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3)
    & k1_xboole_0 != sK3
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
    & v1_funct_2(sK4,k1_tarski(sK2),sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f12,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3)
      & k1_xboole_0 != sK3
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
      & v1_funct_2(sK4,k1_tarski(sK2),sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

fof(f173,plain,
    ( r2_hidden(k1_funct_1(sK4,sK2),sK3)
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(resolution,[],[f172,f128])).

fof(f128,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f66,f122])).

fof(f122,plain,
    ( k1_enumset1(sK2,sK2,sK2) = k1_relat_1(sK4)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl6_5
  <=> k1_enumset1(sK2,sK2,sK2) = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f66,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3))) ),
    inference(definition_unfolding,[],[f38,f65])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) ),
    inference(cnf_transformation,[],[f26])).

fof(f172,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | r2_hidden(k1_funct_1(sK4,sK2),X0) )
    | ~ spl6_8 ),
    inference(resolution,[],[f149,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f149,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(sK4,X0)
        | r2_hidden(k1_funct_1(sK4,sK2),X0) )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl6_8
  <=> ! [X0] :
        ( r2_hidden(k1_funct_1(sK4,sK2),X0)
        | ~ v5_relat_1(sK4,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f161,plain,
    ( ~ spl6_5
    | spl6_6 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | ~ spl6_5
    | spl6_6 ),
    inference(resolution,[],[f151,f128])).

fof(f151,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_6 ),
    inference(resolution,[],[f142,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f142,plain,
    ( ~ v1_relat_1(sK4)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl6_6
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f153,plain,(
    spl6_7 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | spl6_7 ),
    inference(resolution,[],[f146,f36])).

fof(f36,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f146,plain,
    ( ~ v1_funct_1(sK4)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl6_7
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f150,plain,
    ( ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f138,f120,f148,f144,f140])).

fof(f138,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK4,sK2),X0)
        | ~ v1_funct_1(sK4)
        | ~ v5_relat_1(sK4,X0)
        | ~ v1_relat_1(sK4) )
    | ~ spl6_5 ),
    inference(resolution,[],[f133,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(X1))
      | r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

fof(f133,plain,
    ( r2_hidden(sK2,k1_relat_1(sK4))
    | ~ spl6_5 ),
    inference(superposition,[],[f79,f122])).

fof(f79,plain,(
    ! [X6,X8,X7] : r2_hidden(X6,k1_enumset1(X7,X8,X6)) ),
    inference(resolution,[],[f76,f73])).

fof(f73,plain,(
    ! [X2,X5,X3,X1] :
      ( ~ sP1(X5,X1,X2,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ( ( sK5(X0,X1,X2,X3) != X0
              & sK5(X0,X1,X2,X3) != X1
              & sK5(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
          & ( sK5(X0,X1,X2,X3) = X0
            | sK5(X0,X1,X2,X3) = X1
            | sK5(X0,X1,X2,X3) = X2
            | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).

fof(f33,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK5(X0,X1,X2,X3) != X0
            & sK5(X0,X1,X2,X3) != X1
            & sK5(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
        & ( sK5(X0,X1,X2,X3) = X0
          | sK5(X0,X1,X2,X3) = X1
          | sK5(X0,X1,X2,X3) = X2
          | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP1(X2,X1,X0,X3)
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
        | ~ sP1(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP1(X2,X1,X0,X3)
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
        | ~ sP1(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X2,X1,X0,X3] :
      ( sP1(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f76,plain,(
    ! [X2,X0,X1] : sP1(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP1(X2,X1,X0,X3) )
      & ( sP1(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP1(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f20,f23])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f126,plain,(
    spl6_4 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl6_4 ),
    inference(resolution,[],[f118,f66])).

fof(f118,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3)))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl6_4
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f124,plain,
    ( ~ spl6_4
    | spl6_5
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f114,f93,f120,f116])).

fof(f93,plain,
    ( spl6_2
  <=> k1_enumset1(sK2,sK2,sK2) = k1_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f114,plain,
    ( k1_enumset1(sK2,sK2,sK2) = k1_relat_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3)))
    | ~ spl6_2 ),
    inference(superposition,[],[f45,f95])).

fof(f95,plain,
    ( k1_enumset1(sK2,sK2,sK2) = k1_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK4)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f111,plain,(
    ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | ~ spl6_3 ),
    inference(trivial_inequality_removal,[],[f109])).

fof(f109,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl6_3 ),
    inference(superposition,[],[f39,f99])).

fof(f99,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl6_3
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f39,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f26])).

fof(f103,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl6_1 ),
    inference(resolution,[],[f91,f67])).

fof(f67,plain,(
    v1_funct_2(sK4,k1_enumset1(sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f37,f65])).

fof(f37,plain,(
    v1_funct_2(sK4,k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f91,plain,
    ( ~ v1_funct_2(sK4,k1_enumset1(sK2,sK2,sK2),sK3)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl6_1
  <=> v1_funct_2(sK4,k1_enumset1(sK2,sK2,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f100,plain,
    ( ~ spl6_1
    | spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f87,f97,f93,f89])).

fof(f87,plain,
    ( k1_xboole_0 = sK3
    | k1_enumset1(sK2,sK2,sK2) = k1_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK4)
    | ~ v1_funct_2(sK4,k1_enumset1(sK2,sK2,sK2),sK3) ),
    inference(resolution,[],[f82,f66])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = X2
      | k1_relset_1(X1,X2,X0) = X1
      | ~ v1_funct_2(X0,X1,X2) ) ),
    inference(resolution,[],[f48,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f19,f21])).

fof(f21,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n004.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:01:39 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.49  % (4353)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (4353)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f100,f103,f111,f124,f126,f150,f153,f161,f175])).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    ~spl6_5 | ~spl6_8),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f174])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    $false | (~spl6_5 | ~spl6_8)),
% 0.21/0.49    inference(resolution,[],[f173,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ~r2_hidden(k1_funct_1(sK4,sK2),sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ~r2_hidden(k1_funct_1(sK4,sK2),sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f12,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK4,sK2),sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.21/0.49    inference(negated_conjecture,[],[f9])).
% 0.21/0.49  fof(f9,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    r2_hidden(k1_funct_1(sK4,sK2),sK3) | (~spl6_5 | ~spl6_8)),
% 0.21/0.49    inference(resolution,[],[f172,f128])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) | ~spl6_5),
% 0.21/0.49    inference(backward_demodulation,[],[f66,f122])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    k1_enumset1(sK2,sK2,sK2) = k1_relat_1(sK4) | ~spl6_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f120])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    spl6_5 <=> k1_enumset1(sK2,sK2,sK2) = k1_relat_1(sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3)))),
% 0.21/0.49    inference(definition_unfolding,[],[f38,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f41,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | r2_hidden(k1_funct_1(sK4,sK2),X0)) ) | ~spl6_8),
% 0.21/0.49    inference(resolution,[],[f149,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    ( ! [X0] : (~v5_relat_1(sK4,X0) | r2_hidden(k1_funct_1(sK4,sK2),X0)) ) | ~spl6_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f148])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    spl6_8 <=> ! [X0] : (r2_hidden(k1_funct_1(sK4,sK2),X0) | ~v5_relat_1(sK4,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    ~spl6_5 | spl6_6),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f160])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    $false | (~spl6_5 | spl6_6)),
% 0.21/0.49    inference(resolution,[],[f151,f128])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_6),
% 0.21/0.49    inference(resolution,[],[f142,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    ~v1_relat_1(sK4) | spl6_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f140])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    spl6_6 <=> v1_relat_1(sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    spl6_7),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f152])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    $false | spl6_7),
% 0.21/0.49    inference(resolution,[],[f146,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    v1_funct_1(sK4)),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    ~v1_funct_1(sK4) | spl6_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f144])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    spl6_7 <=> v1_funct_1(sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    ~spl6_6 | ~spl6_7 | spl6_8 | ~spl6_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f138,f120,f148,f144,f140])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(k1_funct_1(sK4,sK2),X0) | ~v1_funct_1(sK4) | ~v5_relat_1(sK4,X0) | ~v1_relat_1(sK4)) ) | ~spl6_5),
% 0.21/0.49    inference(resolution,[],[f133,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_relat_1(X1)) | r2_hidden(k1_funct_1(X1,X2),X0) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    r2_hidden(sK2,k1_relat_1(sK4)) | ~spl6_5),
% 0.21/0.49    inference(superposition,[],[f79,f122])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X6,X8,X7] : (r2_hidden(X6,k1_enumset1(X7,X8,X6))) )),
% 0.21/0.49    inference(resolution,[],[f76,f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X2,X5,X3,X1] : (~sP1(X5,X1,X2,X3) | r2_hidden(X5,X3)) )),
% 0.21/0.49    inference(equality_resolution,[],[f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | ~sP1(X0,X1,X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | (((sK5(X0,X1,X2,X3) != X0 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X2) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X0 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X2 | r2_hidden(sK5(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK5(X0,X1,X2,X3) != X0 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X2) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X0 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X2 | r2_hidden(sK5(X0,X1,X2,X3),X3))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.21/0.49    inference(rectify,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X2,X1,X0,X3] : ((sP1(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP1(X2,X1,X0,X3)))),
% 0.21/0.49    inference(flattening,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X2,X1,X0,X3] : ((sP1(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP1(X2,X1,X0,X3)))),
% 0.21/0.49    inference(nnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X2,X1,X0,X3] : (sP1(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (sP1(X2,X1,X0,k1_enumset1(X0,X1,X2))) )),
% 0.21/0.49    inference(equality_resolution,[],[f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (sP1(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP1(X2,X1,X0,X3)) & (sP1(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.49    inference(nnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP1(X2,X1,X0,X3))),
% 0.21/0.49    inference(definition_folding,[],[f20,f23])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    spl6_4),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f125])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    $false | spl6_4),
% 0.21/0.49    inference(resolution,[],[f118,f66])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3))) | spl6_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f116])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    spl6_4 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ~spl6_4 | spl6_5 | ~spl6_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f114,f93,f120,f116])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    spl6_2 <=> k1_enumset1(sK2,sK2,sK2) = k1_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    k1_enumset1(sK2,sK2,sK2) = k1_relat_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3))) | ~spl6_2),
% 0.21/0.49    inference(superposition,[],[f45,f95])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    k1_enumset1(sK2,sK2,sK2) = k1_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK4) | ~spl6_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f93])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ~spl6_3),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f110])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    $false | ~spl6_3),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f109])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    k1_xboole_0 != k1_xboole_0 | ~spl6_3),
% 0.21/0.49    inference(superposition,[],[f39,f99])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    k1_xboole_0 = sK3 | ~spl6_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f97])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    spl6_3 <=> k1_xboole_0 = sK3),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    k1_xboole_0 != sK3),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    spl6_1),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f101])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    $false | spl6_1),
% 0.21/0.49    inference(resolution,[],[f91,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    v1_funct_2(sK4,k1_enumset1(sK2,sK2,sK2),sK3)),
% 0.21/0.49    inference(definition_unfolding,[],[f37,f65])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    v1_funct_2(sK4,k1_tarski(sK2),sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ~v1_funct_2(sK4,k1_enumset1(sK2,sK2,sK2),sK3) | spl6_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    spl6_1 <=> v1_funct_2(sK4,k1_enumset1(sK2,sK2,sK2),sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    ~spl6_1 | spl6_2 | spl6_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f87,f97,f93,f89])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    k1_xboole_0 = sK3 | k1_enumset1(sK2,sK2,sK2) = k1_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK4) | ~v1_funct_2(sK4,k1_enumset1(sK2,sK2,sK2),sK3)),
% 0.21/0.49    inference(resolution,[],[f82,f66])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = X2 | k1_relset_1(X1,X2,X0) = X1 | ~v1_funct_2(X0,X1,X2)) )),
% 0.21/0.49    inference(resolution,[],[f48,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (sP0(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(definition_folding,[],[f19,f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 0.21/0.49    inference(rectify,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f21])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (4353)------------------------------
% 0.21/0.49  % (4353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (4353)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (4353)Memory used [KB]: 6268
% 0.21/0.49  % (4353)Time elapsed: 0.093 s
% 0.21/0.49  % (4353)------------------------------
% 0.21/0.49  % (4353)------------------------------
% 0.21/0.50  % (4343)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (4340)Success in time 0.138 s
%------------------------------------------------------------------------------
