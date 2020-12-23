%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:25 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 403 expanded)
%              Number of leaves         :   29 ( 134 expanded)
%              Depth                    :   14
%              Number of atoms          :  454 (1180 expanded)
%              Number of equality atoms :  104 ( 378 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f435,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f223,f225,f227,f258,f297,f312,f313,f343,f386,f434])).

fof(f434,plain,
    ( ~ spl8_15
    | ~ spl8_16
    | ~ spl8_20 ),
    inference(avatar_contradiction_clause,[],[f431])).

fof(f431,plain,
    ( $false
    | ~ spl8_15
    | ~ spl8_16
    | ~ spl8_20 ),
    inference(resolution,[],[f421,f134])).

fof(f134,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f104,f120])).

fof(f120,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f79,f119])).

fof(f119,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f89,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f89,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f79,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f104,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f421,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ spl8_15
    | ~ spl8_16
    | ~ spl8_20 ),
    inference(backward_demodulation,[],[f167,f417])).

fof(f417,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(sK3,X0)
    | ~ spl8_15
    | ~ spl8_16
    | ~ spl8_20 ),
    inference(resolution,[],[f408,f385])).

fof(f385,plain,
    ( ! [X1] : r1_tarski(k9_relat_1(sK3,X1),k1_xboole_0)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f384])).

fof(f384,plain,
    ( spl8_20
  <=> ! [X1] : r1_tarski(k9_relat_1(sK3,X1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f408,plain,
    ( ! [X9] :
        ( ~ r1_tarski(X9,k1_xboole_0)
        | k1_xboole_0 = X9 )
    | ~ spl8_15
    | ~ spl8_16 ),
    inference(resolution,[],[f350,f374])).

fof(f374,plain,
    ( ! [X3] :
        ( r2_hidden(sK4(sK3,X3),X3)
        | k1_xboole_0 = X3 )
    | ~ spl8_15
    | ~ spl8_16 ),
    inference(backward_demodulation,[],[f347,f366])).

fof(f366,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ spl8_15
    | ~ spl8_16 ),
    inference(resolution,[],[f346,f77])).

fof(f77,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f346,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK4(sK3,X1))
        | k2_relat_1(sK3) = X1 )
    | ~ spl8_15
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f327,f342])).

fof(f342,plain,
    ( ! [X2] : ~ r2_hidden(X2,k1_xboole_0)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f341])).

fof(f341,plain,
    ( spl8_16
  <=> ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f327,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(sK3,X1),k1_xboole_0)
        | k2_relat_1(sK3) = X1
        | ~ r1_tarski(X1,sK4(sK3,X1)) )
    | ~ spl8_15 ),
    inference(resolution,[],[f241,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f241,plain,
    ( ! [X3] :
        ( r2_hidden(sK5(sK3,X3),k1_xboole_0)
        | r2_hidden(sK4(sK3,X3),X3)
        | k2_relat_1(sK3) = X3 )
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl8_15
  <=> ! [X3] :
        ( r2_hidden(sK5(sK3,X3),k1_xboole_0)
        | k2_relat_1(sK3) = X3
        | r2_hidden(sK4(sK3,X3),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f347,plain,
    ( ! [X3] :
        ( r2_hidden(sK4(sK3,X3),X3)
        | k2_relat_1(sK3) = X3 )
    | ~ spl8_15
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f241,f342])).

fof(f350,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,k1_xboole_0) )
    | ~ spl8_16 ),
    inference(resolution,[],[f342,f100])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f65,f66])).

fof(f66,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
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

fof(f167,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f121,f137])).

fof(f137,plain,(
    ! [X0] : k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f122,f117])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f122,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f74,f120])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f52])).

fof(f52,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

fof(f121,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f76,f120,f120])).

fof(f76,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f386,plain,
    ( ~ spl8_10
    | spl8_20
    | ~ spl8_15
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f376,f341,f240,f384,f215])).

fof(f215,plain,
    ( spl8_10
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f376,plain,
    ( ! [X1] :
        ( r1_tarski(k9_relat_1(sK3,X1),k1_xboole_0)
        | ~ v1_relat_1(sK3) )
    | ~ spl8_15
    | ~ spl8_16 ),
    inference(superposition,[],[f90,f366])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(f343,plain,
    ( ~ spl8_10
    | ~ spl8_11
    | spl8_16
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f339,f236,f175,f341,f218,f215])).

fof(f218,plain,
    ( spl8_11
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f175,plain,
    ( spl8_6
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f236,plain,
    ( spl8_14
  <=> ! [X2] :
        ( r2_hidden(sK6(sK3,X2),k1_xboole_0)
        | ~ r2_hidden(X2,k2_relat_1(sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f339,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_xboole_0)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(forward_demodulation,[],[f333,f176])).

fof(f176,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f175])).

fof(f333,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_relat_1(sK3))
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl8_14 ),
    inference(resolution,[],[f328,f128])).

fof(f128,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f127])).

fof(f127,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK4(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK4(X0,X1),X1) )
              & ( ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
                  & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK4(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK6(X0,X5)) = X5
                    & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f55,f58,f57,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK4(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK4(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK4(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f54])).

% (13821)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (13823)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (13812)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (13822)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (13820)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (13800)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f328,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_relat_1(sK3))
    | ~ spl8_14 ),
    inference(resolution,[],[f324,f77])).

fof(f324,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,sK6(sK3,X0))
        | ~ r2_hidden(X0,k2_relat_1(sK3)) )
    | ~ spl8_14 ),
    inference(resolution,[],[f237,f111])).

fof(f237,plain,
    ( ! [X2] :
        ( r2_hidden(sK6(sK3,X2),k1_xboole_0)
        | ~ r2_hidden(X2,k2_relat_1(sK3)) )
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f236])).

fof(f313,plain,
    ( ~ spl8_10
    | ~ spl8_11
    | spl8_15
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f309,f175,f240,f218,f215])).

fof(f309,plain,
    ( ! [X3] :
        ( r2_hidden(sK5(sK3,X3),k1_xboole_0)
        | r2_hidden(sK4(sK3,X3),X3)
        | k2_relat_1(sK3) = X3
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl8_6 ),
    inference(superposition,[],[f85,f176])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK4(X0,X1),X1)
      | k2_relat_1(X0) = X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f312,plain,
    ( ~ spl8_10
    | ~ spl8_11
    | spl8_14
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f308,f175,f236,f218,f215])).

fof(f308,plain,
    ( ! [X2] :
        ( r2_hidden(sK6(sK3,X2),k1_xboole_0)
        | ~ r2_hidden(X2,k2_relat_1(sK3))
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl8_6 ),
    inference(superposition,[],[f130,f176])).

fof(f130,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f297,plain,(
    ~ spl8_12 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f140,f295])).

fof(f295,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl8_12 ),
    inference(resolution,[],[f290,f90])).

fof(f290,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl8_12 ),
    inference(backward_demodulation,[],[f167,f222])).

fof(f222,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl8_12
  <=> k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f140,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f122,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f258,plain,
    ( spl8_5
    | spl8_6 ),
    inference(avatar_split_clause,[],[f255,f175,f172])).

fof(f172,plain,
    ( spl8_5
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f255,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
    inference(resolution,[],[f158,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f103,f120,f120])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f158,plain,(
    r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(global_subsumption,[],[f140,f157])).

fof(f157,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f138,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f138,plain,(
    v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f122,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f227,plain,(
    spl8_11 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | spl8_11 ),
    inference(subsumption_resolution,[],[f73,f219])).

fof(f219,plain,
    ( ~ v1_funct_1(sK3)
    | spl8_11 ),
    inference(avatar_component_clause,[],[f218])).

fof(f73,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f225,plain,(
    spl8_10 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | spl8_10 ),
    inference(subsumption_resolution,[],[f140,f216])).

fof(f216,plain,
    ( ~ v1_relat_1(sK3)
    | spl8_10 ),
    inference(avatar_component_clause,[],[f215])).

fof(f223,plain,
    ( ~ spl8_10
    | ~ spl8_11
    | spl8_12
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f213,f172,f221,f218,f215])).

fof(f213,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_5 ),
    inference(equality_resolution,[],[f192])).

fof(f192,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != k1_relat_1(sK3)
        | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,sK0),k1_funct_1(X1,sK0),k1_funct_1(X1,sK0),k1_funct_1(X1,sK0))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl8_5 ),
    inference(superposition,[],[f123,f173])).

fof(f173,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f172])).

fof(f123,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0)
      | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f96,f120,f120])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n014.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 20:27:37 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.18/0.45  % (13808)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.47  % (13824)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.18/0.52  % (13818)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.18/0.52  % (13810)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.18/0.53  % (13796)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.18/0.53  % (13818)Refutation not found, incomplete strategy% (13818)------------------------------
% 0.18/0.53  % (13818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.53  % (13818)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.53  
% 0.18/0.53  % (13818)Memory used [KB]: 10746
% 0.18/0.53  % (13818)Time elapsed: 0.064 s
% 0.18/0.53  % (13818)------------------------------
% 0.18/0.53  % (13818)------------------------------
% 0.18/0.54  % (13819)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.18/0.54  % (13805)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.18/0.54  % (13799)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.18/0.54  % (13802)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.18/0.54  % (13806)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.18/0.54  % (13801)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.18/0.55  % (13825)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.18/0.55  % (13803)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.18/0.55  % (13814)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.18/0.55  % (13813)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.18/0.55  % (13798)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.18/0.55  % (13811)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.18/0.55  % (13809)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.18/0.56  % (13804)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.18/0.56  % (13817)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.18/0.56  % (13797)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.18/0.56  % (13798)Refutation found. Thanks to Tanya!
% 0.18/0.56  % SZS status Theorem for theBenchmark
% 0.18/0.56  % SZS output start Proof for theBenchmark
% 0.18/0.56  fof(f435,plain,(
% 0.18/0.56    $false),
% 0.18/0.56    inference(avatar_sat_refutation,[],[f223,f225,f227,f258,f297,f312,f313,f343,f386,f434])).
% 0.18/0.56  fof(f434,plain,(
% 0.18/0.56    ~spl8_15 | ~spl8_16 | ~spl8_20),
% 0.18/0.56    inference(avatar_contradiction_clause,[],[f431])).
% 0.18/0.56  fof(f431,plain,(
% 0.18/0.56    $false | (~spl8_15 | ~spl8_16 | ~spl8_20)),
% 0.18/0.56    inference(resolution,[],[f421,f134])).
% 0.18/0.56  fof(f134,plain,(
% 0.18/0.56    ( ! [X1] : (r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1))) )),
% 0.18/0.56    inference(equality_resolution,[],[f125])).
% 0.18/0.56  fof(f125,plain,(
% 0.18/0.56    ( ! [X0,X1] : (r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 != X0) )),
% 0.18/0.56    inference(definition_unfolding,[],[f104,f120])).
% 0.18/0.56  fof(f120,plain,(
% 0.18/0.56    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.18/0.56    inference(definition_unfolding,[],[f79,f119])).
% 0.18/0.56  fof(f119,plain,(
% 0.18/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.18/0.56    inference(definition_unfolding,[],[f89,f112])).
% 0.18/0.56  fof(f112,plain,(
% 0.18/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.18/0.56    inference(cnf_transformation,[],[f6])).
% 0.18/0.56  fof(f6,axiom,(
% 0.18/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.18/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.18/0.56  fof(f89,plain,(
% 0.18/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.18/0.56    inference(cnf_transformation,[],[f5])).
% 0.18/0.56  fof(f5,axiom,(
% 0.18/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.18/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.18/0.56  fof(f79,plain,(
% 0.18/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.18/0.56    inference(cnf_transformation,[],[f4])).
% 0.18/0.56  fof(f4,axiom,(
% 0.18/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.18/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.18/0.56  fof(f104,plain,(
% 0.18/0.56    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 0.18/0.56    inference(cnf_transformation,[],[f69])).
% 0.18/0.56  fof(f69,plain,(
% 0.18/0.56    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.18/0.56    inference(flattening,[],[f68])).
% 0.18/0.56  fof(f68,plain,(
% 0.18/0.56    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.18/0.56    inference(nnf_transformation,[],[f7])).
% 0.18/0.56  fof(f7,axiom,(
% 0.18/0.56    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.18/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.18/0.56  fof(f421,plain,(
% 0.18/0.56    ~r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) | (~spl8_15 | ~spl8_16 | ~spl8_20)),
% 0.18/0.56    inference(backward_demodulation,[],[f167,f417])).
% 0.18/0.56  fof(f417,plain,(
% 0.18/0.56    ( ! [X0] : (k1_xboole_0 = k9_relat_1(sK3,X0)) ) | (~spl8_15 | ~spl8_16 | ~spl8_20)),
% 0.18/0.56    inference(resolution,[],[f408,f385])).
% 0.18/0.56  fof(f385,plain,(
% 0.18/0.56    ( ! [X1] : (r1_tarski(k9_relat_1(sK3,X1),k1_xboole_0)) ) | ~spl8_20),
% 0.18/0.56    inference(avatar_component_clause,[],[f384])).
% 0.18/0.56  fof(f384,plain,(
% 0.18/0.56    spl8_20 <=> ! [X1] : r1_tarski(k9_relat_1(sK3,X1),k1_xboole_0)),
% 0.18/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.18/0.56  fof(f408,plain,(
% 0.18/0.56    ( ! [X9] : (~r1_tarski(X9,k1_xboole_0) | k1_xboole_0 = X9) ) | (~spl8_15 | ~spl8_16)),
% 0.18/0.56    inference(resolution,[],[f350,f374])).
% 0.18/0.56  fof(f374,plain,(
% 0.18/0.56    ( ! [X3] : (r2_hidden(sK4(sK3,X3),X3) | k1_xboole_0 = X3) ) | (~spl8_15 | ~spl8_16)),
% 0.18/0.56    inference(backward_demodulation,[],[f347,f366])).
% 0.18/0.56  fof(f366,plain,(
% 0.18/0.56    k1_xboole_0 = k2_relat_1(sK3) | (~spl8_15 | ~spl8_16)),
% 0.18/0.56    inference(resolution,[],[f346,f77])).
% 0.18/0.56  fof(f77,plain,(
% 0.18/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.18/0.56    inference(cnf_transformation,[],[f3])).
% 0.18/0.56  fof(f3,axiom,(
% 0.18/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.18/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.18/0.56  fof(f346,plain,(
% 0.18/0.56    ( ! [X1] : (~r1_tarski(X1,sK4(sK3,X1)) | k2_relat_1(sK3) = X1) ) | (~spl8_15 | ~spl8_16)),
% 0.18/0.56    inference(subsumption_resolution,[],[f327,f342])).
% 0.18/0.56  fof(f342,plain,(
% 0.18/0.56    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) ) | ~spl8_16),
% 0.18/0.56    inference(avatar_component_clause,[],[f341])).
% 0.18/0.56  fof(f341,plain,(
% 0.18/0.56    spl8_16 <=> ! [X2] : ~r2_hidden(X2,k1_xboole_0)),
% 0.18/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.18/0.56  fof(f327,plain,(
% 0.18/0.56    ( ! [X1] : (r2_hidden(sK5(sK3,X1),k1_xboole_0) | k2_relat_1(sK3) = X1 | ~r1_tarski(X1,sK4(sK3,X1))) ) | ~spl8_15),
% 0.18/0.56    inference(resolution,[],[f241,f111])).
% 0.18/0.56  fof(f111,plain,(
% 0.18/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.18/0.56    inference(cnf_transformation,[],[f44])).
% 0.18/0.56  fof(f44,plain,(
% 0.18/0.56    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.18/0.56    inference(ennf_transformation,[],[f21])).
% 0.18/0.56  fof(f21,axiom,(
% 0.18/0.56    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.18/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.18/0.56  fof(f241,plain,(
% 0.18/0.56    ( ! [X3] : (r2_hidden(sK5(sK3,X3),k1_xboole_0) | r2_hidden(sK4(sK3,X3),X3) | k2_relat_1(sK3) = X3) ) | ~spl8_15),
% 0.18/0.56    inference(avatar_component_clause,[],[f240])).
% 0.18/0.56  fof(f240,plain,(
% 0.18/0.56    spl8_15 <=> ! [X3] : (r2_hidden(sK5(sK3,X3),k1_xboole_0) | k2_relat_1(sK3) = X3 | r2_hidden(sK4(sK3,X3),X3))),
% 0.18/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.18/0.56  fof(f347,plain,(
% 0.18/0.56    ( ! [X3] : (r2_hidden(sK4(sK3,X3),X3) | k2_relat_1(sK3) = X3) ) | (~spl8_15 | ~spl8_16)),
% 0.18/0.56    inference(subsumption_resolution,[],[f241,f342])).
% 0.18/0.56  fof(f350,plain,(
% 0.18/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,k1_xboole_0)) ) | ~spl8_16),
% 0.18/0.56    inference(resolution,[],[f342,f100])).
% 0.18/0.56  fof(f100,plain,(
% 0.18/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.18/0.56    inference(cnf_transformation,[],[f67])).
% 0.18/0.56  fof(f67,plain,(
% 0.18/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.18/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f65,f66])).
% 0.18/0.56  fof(f66,plain,(
% 0.18/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 0.18/0.56    introduced(choice_axiom,[])).
% 0.18/0.56  fof(f65,plain,(
% 0.18/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.18/0.56    inference(rectify,[],[f64])).
% 0.18/0.56  fof(f64,plain,(
% 0.18/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.18/0.56    inference(nnf_transformation,[],[f43])).
% 0.18/0.56  fof(f43,plain,(
% 0.18/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.18/0.56    inference(ennf_transformation,[],[f1])).
% 0.18/0.56  fof(f1,axiom,(
% 0.18/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.18/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.18/0.56  fof(f167,plain,(
% 0.18/0.56    ~r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 0.18/0.56    inference(backward_demodulation,[],[f121,f137])).
% 0.18/0.56  fof(f137,plain,(
% 0.18/0.56    ( ! [X0] : (k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 0.18/0.56    inference(resolution,[],[f122,f117])).
% 0.18/0.56  fof(f117,plain,(
% 0.18/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.18/0.56    inference(cnf_transformation,[],[f49])).
% 0.18/0.56  fof(f49,plain,(
% 0.18/0.56    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.56    inference(ennf_transformation,[],[f24])).
% 0.18/0.56  fof(f24,axiom,(
% 0.18/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.18/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.18/0.56  fof(f122,plain,(
% 0.18/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.18/0.56    inference(definition_unfolding,[],[f74,f120])).
% 0.18/0.56  fof(f74,plain,(
% 0.18/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.18/0.56    inference(cnf_transformation,[],[f53])).
% 0.18/0.56  fof(f53,plain,(
% 0.18/0.56    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 0.18/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f52])).
% 0.18/0.56  fof(f52,plain,(
% 0.18/0.56    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 0.18/0.56    introduced(choice_axiom,[])).
% 0.18/0.56  fof(f30,plain,(
% 0.18/0.56    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 0.18/0.56    inference(flattening,[],[f29])).
% 0.18/0.56  fof(f29,plain,(
% 0.18/0.56    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 0.18/0.56    inference(ennf_transformation,[],[f28])).
% 0.18/0.56  fof(f28,plain,(
% 0.18/0.56    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.18/0.56    inference(pure_predicate_removal,[],[f27])).
% 0.18/0.56  fof(f27,negated_conjecture,(
% 0.18/0.56    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.18/0.56    inference(negated_conjecture,[],[f26])).
% 0.18/0.56  fof(f26,conjecture,(
% 0.18/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.18/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).
% 0.18/0.56  fof(f121,plain,(
% 0.18/0.56    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 0.18/0.56    inference(definition_unfolding,[],[f76,f120,f120])).
% 0.18/0.56  fof(f76,plain,(
% 0.18/0.56    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 0.18/0.56    inference(cnf_transformation,[],[f53])).
% 0.18/0.56  fof(f386,plain,(
% 0.18/0.56    ~spl8_10 | spl8_20 | ~spl8_15 | ~spl8_16),
% 0.18/0.56    inference(avatar_split_clause,[],[f376,f341,f240,f384,f215])).
% 0.18/0.56  fof(f215,plain,(
% 0.18/0.56    spl8_10 <=> v1_relat_1(sK3)),
% 0.18/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.18/0.56  fof(f376,plain,(
% 0.18/0.56    ( ! [X1] : (r1_tarski(k9_relat_1(sK3,X1),k1_xboole_0) | ~v1_relat_1(sK3)) ) | (~spl8_15 | ~spl8_16)),
% 0.18/0.56    inference(superposition,[],[f90,f366])).
% 0.18/0.56  fof(f90,plain,(
% 0.18/0.56    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.18/0.56    inference(cnf_transformation,[],[f36])).
% 0.18/0.56  fof(f36,plain,(
% 0.18/0.56    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.18/0.56    inference(ennf_transformation,[],[f16])).
% 0.18/0.56  fof(f16,axiom,(
% 0.18/0.56    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 0.18/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).
% 0.18/0.56  fof(f343,plain,(
% 0.18/0.56    ~spl8_10 | ~spl8_11 | spl8_16 | ~spl8_6 | ~spl8_14),
% 0.18/0.56    inference(avatar_split_clause,[],[f339,f236,f175,f341,f218,f215])).
% 0.18/0.56  fof(f218,plain,(
% 0.18/0.56    spl8_11 <=> v1_funct_1(sK3)),
% 0.18/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.18/0.56  fof(f175,plain,(
% 0.18/0.56    spl8_6 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 0.18/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.18/0.56  fof(f236,plain,(
% 0.18/0.56    spl8_14 <=> ! [X2] : (r2_hidden(sK6(sK3,X2),k1_xboole_0) | ~r2_hidden(X2,k2_relat_1(sK3)))),
% 0.18/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.18/0.56  fof(f339,plain,(
% 0.18/0.56    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | (~spl8_6 | ~spl8_14)),
% 0.18/0.56    inference(forward_demodulation,[],[f333,f176])).
% 0.18/0.56  fof(f176,plain,(
% 0.18/0.56    k1_xboole_0 = k1_relat_1(sK3) | ~spl8_6),
% 0.18/0.56    inference(avatar_component_clause,[],[f175])).
% 0.18/0.56  fof(f333,plain,(
% 0.18/0.56    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | ~spl8_14),
% 0.18/0.56    inference(resolution,[],[f328,f128])).
% 0.18/0.56  fof(f128,plain,(
% 0.18/0.56    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.56    inference(equality_resolution,[],[f127])).
% 0.18/0.56  fof(f127,plain,(
% 0.18/0.56    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.56    inference(equality_resolution,[],[f84])).
% 0.18/0.56  fof(f84,plain,(
% 0.18/0.56    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.56    inference(cnf_transformation,[],[f59])).
% 0.18/0.56  fof(f59,plain,(
% 0.18/0.56    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & ((sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.18/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f55,f58,f57,f56])).
% 0.18/0.56  fof(f56,plain,(
% 0.18/0.56    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1))))),
% 0.18/0.56    introduced(choice_axiom,[])).
% 0.18/0.56  fof(f57,plain,(
% 0.18/0.56    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 0.18/0.56    introduced(choice_axiom,[])).
% 0.18/0.56  fof(f58,plain,(
% 0.18/0.56    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))))),
% 0.18/0.56    introduced(choice_axiom,[])).
% 0.18/0.56  fof(f55,plain,(
% 0.18/0.56    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.18/0.56    inference(rectify,[],[f54])).
% 0.18/0.56  % (13821)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.18/0.56  % (13823)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.18/0.57  % (13812)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.18/0.57  % (13822)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.18/0.57  % (13820)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.18/0.58  % (13800)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.81/0.58  fof(f54,plain,(
% 1.81/0.58    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.81/0.58    inference(nnf_transformation,[],[f35])).
% 1.81/0.58  fof(f35,plain,(
% 1.81/0.58    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.81/0.58    inference(flattening,[],[f34])).
% 1.81/0.58  fof(f34,plain,(
% 1.81/0.58    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.81/0.58    inference(ennf_transformation,[],[f19])).
% 1.81/0.58  fof(f19,axiom,(
% 1.81/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.81/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 1.81/0.58  fof(f328,plain,(
% 1.81/0.58    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3))) ) | ~spl8_14),
% 1.81/0.58    inference(resolution,[],[f324,f77])).
% 1.81/0.58  fof(f324,plain,(
% 1.81/0.58    ( ! [X0] : (~r1_tarski(k1_xboole_0,sK6(sK3,X0)) | ~r2_hidden(X0,k2_relat_1(sK3))) ) | ~spl8_14),
% 1.81/0.58    inference(resolution,[],[f237,f111])).
% 1.81/0.58  fof(f237,plain,(
% 1.81/0.58    ( ! [X2] : (r2_hidden(sK6(sK3,X2),k1_xboole_0) | ~r2_hidden(X2,k2_relat_1(sK3))) ) | ~spl8_14),
% 1.81/0.58    inference(avatar_component_clause,[],[f236])).
% 1.81/0.58  fof(f313,plain,(
% 1.81/0.58    ~spl8_10 | ~spl8_11 | spl8_15 | ~spl8_6),
% 1.81/0.58    inference(avatar_split_clause,[],[f309,f175,f240,f218,f215])).
% 1.81/0.58  fof(f309,plain,(
% 1.81/0.58    ( ! [X3] : (r2_hidden(sK5(sK3,X3),k1_xboole_0) | r2_hidden(sK4(sK3,X3),X3) | k2_relat_1(sK3) = X3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | ~spl8_6),
% 1.81/0.58    inference(superposition,[],[f85,f176])).
% 1.81/0.58  fof(f85,plain,(
% 1.81/0.58    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | r2_hidden(sK4(X0,X1),X1) | k2_relat_1(X0) = X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.81/0.58    inference(cnf_transformation,[],[f59])).
% 1.81/0.58  fof(f312,plain,(
% 1.81/0.58    ~spl8_10 | ~spl8_11 | spl8_14 | ~spl8_6),
% 1.81/0.58    inference(avatar_split_clause,[],[f308,f175,f236,f218,f215])).
% 1.81/0.58  fof(f308,plain,(
% 1.81/0.58    ( ! [X2] : (r2_hidden(sK6(sK3,X2),k1_xboole_0) | ~r2_hidden(X2,k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | ~spl8_6),
% 1.81/0.58    inference(superposition,[],[f130,f176])).
% 1.81/0.58  fof(f130,plain,(
% 1.81/0.58    ( ! [X0,X5] : (r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.81/0.58    inference(equality_resolution,[],[f82])).
% 1.81/0.58  fof(f82,plain,(
% 1.81/0.58    ( ! [X0,X5,X1] : (r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.81/0.58    inference(cnf_transformation,[],[f59])).
% 1.81/0.58  fof(f297,plain,(
% 1.81/0.58    ~spl8_12),
% 1.81/0.58    inference(avatar_contradiction_clause,[],[f296])).
% 1.81/0.58  fof(f296,plain,(
% 1.81/0.58    $false | ~spl8_12),
% 1.81/0.58    inference(subsumption_resolution,[],[f140,f295])).
% 1.81/0.58  fof(f295,plain,(
% 1.81/0.58    ~v1_relat_1(sK3) | ~spl8_12),
% 1.81/0.58    inference(resolution,[],[f290,f90])).
% 1.81/0.58  fof(f290,plain,(
% 1.81/0.58    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~spl8_12),
% 1.81/0.58    inference(backward_demodulation,[],[f167,f222])).
% 1.81/0.58  fof(f222,plain,(
% 1.81/0.58    k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~spl8_12),
% 1.81/0.58    inference(avatar_component_clause,[],[f221])).
% 1.81/0.58  fof(f221,plain,(
% 1.81/0.58    spl8_12 <=> k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)),
% 1.81/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.81/0.58  fof(f140,plain,(
% 1.81/0.58    v1_relat_1(sK3)),
% 1.81/0.58    inference(resolution,[],[f122,f113])).
% 1.81/0.58  fof(f113,plain,(
% 1.81/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.81/0.58    inference(cnf_transformation,[],[f45])).
% 1.81/0.58  fof(f45,plain,(
% 1.81/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.81/0.58    inference(ennf_transformation,[],[f22])).
% 1.81/0.58  fof(f22,axiom,(
% 1.81/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.81/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.81/0.58  fof(f258,plain,(
% 1.81/0.58    spl8_5 | spl8_6),
% 1.81/0.58    inference(avatar_split_clause,[],[f255,f175,f172])).
% 1.81/0.58  fof(f172,plain,(
% 1.81/0.58    spl8_5 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)),
% 1.81/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.81/0.58  fof(f255,plain,(
% 1.81/0.58    k1_xboole_0 = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)),
% 1.81/0.58    inference(resolution,[],[f158,f126])).
% 1.81/0.58  fof(f126,plain,(
% 1.81/0.58    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 1.81/0.58    inference(definition_unfolding,[],[f103,f120,f120])).
% 1.81/0.58  fof(f103,plain,(
% 1.81/0.58    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.81/0.58    inference(cnf_transformation,[],[f69])).
% 1.81/0.58  fof(f158,plain,(
% 1.81/0.58    r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.81/0.58    inference(global_subsumption,[],[f140,f157])).
% 1.81/0.58  fof(f157,plain,(
% 1.81/0.58    r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK3)),
% 1.81/0.58    inference(resolution,[],[f138,f91])).
% 1.81/0.58  fof(f91,plain,(
% 1.81/0.58    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.81/0.58    inference(cnf_transformation,[],[f60])).
% 1.81/0.58  fof(f60,plain,(
% 1.81/0.58    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.81/0.58    inference(nnf_transformation,[],[f37])).
% 1.81/0.58  fof(f37,plain,(
% 1.81/0.58    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.81/0.58    inference(ennf_transformation,[],[f13])).
% 1.81/0.58  fof(f13,axiom,(
% 1.81/0.58    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.81/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.81/0.58  fof(f138,plain,(
% 1.81/0.58    v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.81/0.58    inference(resolution,[],[f122,f114])).
% 1.81/0.58  fof(f114,plain,(
% 1.81/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.81/0.58    inference(cnf_transformation,[],[f46])).
% 1.81/0.58  fof(f46,plain,(
% 1.81/0.58    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.81/0.58    inference(ennf_transformation,[],[f23])).
% 1.81/0.58  fof(f23,axiom,(
% 1.81/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.81/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.81/0.58  fof(f227,plain,(
% 1.81/0.58    spl8_11),
% 1.81/0.58    inference(avatar_contradiction_clause,[],[f226])).
% 1.81/0.58  fof(f226,plain,(
% 1.81/0.58    $false | spl8_11),
% 1.81/0.58    inference(subsumption_resolution,[],[f73,f219])).
% 1.81/0.58  fof(f219,plain,(
% 1.81/0.58    ~v1_funct_1(sK3) | spl8_11),
% 1.81/0.58    inference(avatar_component_clause,[],[f218])).
% 1.81/0.58  fof(f73,plain,(
% 1.81/0.58    v1_funct_1(sK3)),
% 1.81/0.58    inference(cnf_transformation,[],[f53])).
% 1.81/0.58  fof(f225,plain,(
% 1.81/0.58    spl8_10),
% 1.81/0.58    inference(avatar_contradiction_clause,[],[f224])).
% 1.81/0.58  fof(f224,plain,(
% 1.81/0.58    $false | spl8_10),
% 1.81/0.58    inference(subsumption_resolution,[],[f140,f216])).
% 1.81/0.58  fof(f216,plain,(
% 1.81/0.58    ~v1_relat_1(sK3) | spl8_10),
% 1.81/0.58    inference(avatar_component_clause,[],[f215])).
% 1.81/0.58  fof(f223,plain,(
% 1.81/0.58    ~spl8_10 | ~spl8_11 | spl8_12 | ~spl8_5),
% 1.81/0.58    inference(avatar_split_clause,[],[f213,f172,f221,f218,f215])).
% 1.81/0.58  fof(f213,plain,(
% 1.81/0.58    k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl8_5),
% 1.81/0.58    inference(equality_resolution,[],[f192])).
% 1.81/0.58  fof(f192,plain,(
% 1.81/0.58    ( ! [X1] : (k1_relat_1(X1) != k1_relat_1(sK3) | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,sK0),k1_funct_1(X1,sK0),k1_funct_1(X1,sK0),k1_funct_1(X1,sK0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | ~spl8_5),
% 1.81/0.58    inference(superposition,[],[f123,f173])).
% 1.81/0.58  fof(f173,plain,(
% 1.81/0.58    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | ~spl8_5),
% 1.81/0.58    inference(avatar_component_clause,[],[f172])).
% 1.81/0.58  fof(f123,plain,(
% 1.81/0.58    ( ! [X0,X1] : (k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0) | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.81/0.58    inference(definition_unfolding,[],[f96,f120,f120])).
% 1.81/0.58  fof(f96,plain,(
% 1.81/0.58    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.81/0.58    inference(cnf_transformation,[],[f42])).
% 1.81/0.58  fof(f42,plain,(
% 1.81/0.58    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.81/0.58    inference(flattening,[],[f41])).
% 1.81/0.58  fof(f41,plain,(
% 1.81/0.58    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.81/0.58    inference(ennf_transformation,[],[f20])).
% 1.81/0.58  fof(f20,axiom,(
% 1.81/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.81/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 1.81/0.58  % SZS output end Proof for theBenchmark
% 1.81/0.58  % (13798)------------------------------
% 1.81/0.58  % (13798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.58  % (13798)Termination reason: Refutation
% 1.81/0.58  
% 1.81/0.58  % (13798)Memory used [KB]: 10874
% 1.81/0.58  % (13798)Time elapsed: 0.173 s
% 1.81/0.58  % (13798)------------------------------
% 1.81/0.58  % (13798)------------------------------
% 1.81/0.58  % (13795)Success in time 0.24 s
%------------------------------------------------------------------------------
