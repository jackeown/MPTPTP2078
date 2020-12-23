%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 203 expanded)
%              Number of leaves         :   30 (  82 expanded)
%              Depth                    :   12
%              Number of atoms          :  404 ( 738 expanded)
%              Number of equality atoms :   26 (  54 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f437,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f93,f114,f130,f136,f145,f295,f305,f321,f326,f332,f384,f436])).

fof(f436,plain,
    ( ~ spl10_20
    | ~ spl10_21
    | ~ spl10_27 ),
    inference(avatar_contradiction_clause,[],[f435])).

fof(f435,plain,
    ( $false
    | ~ spl10_20
    | ~ spl10_21
    | ~ spl10_27 ),
    inference(subsumption_resolution,[],[f434,f315])).

fof(f315,plain,
    ( m1_subset_1(sK9(sK6,sK7,sK8),sK4)
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f313])).

fof(f313,plain,
    ( spl10_20
  <=> m1_subset_1(sK9(sK6,sK7,sK8),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f434,plain,
    ( ~ m1_subset_1(sK9(sK6,sK7,sK8),sK4)
    | ~ spl10_21
    | ~ spl10_27 ),
    inference(subsumption_resolution,[],[f429,f320])).

fof(f320,plain,
    ( r2_hidden(sK9(sK6,sK7,sK8),sK6)
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f318])).

fof(f318,plain,
    ( spl10_21
  <=> r2_hidden(sK9(sK6,sK7,sK8),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f429,plain,
    ( ~ r2_hidden(sK9(sK6,sK7,sK8),sK6)
    | ~ m1_subset_1(sK9(sK6,sK7,sK8),sK4)
    | ~ spl10_27 ),
    inference(trivial_inequality_removal,[],[f426])).

fof(f426,plain,
    ( ~ r2_hidden(sK9(sK6,sK7,sK8),sK6)
    | ~ m1_subset_1(sK9(sK6,sK7,sK8),sK4)
    | sK8 != sK8
    | ~ spl10_27 ),
    inference(resolution,[],[f375,f214])).

fof(f214,plain,(
    ! [X0,X1] :
      ( ~ sP2(X1,X0,sK7)
      | ~ r2_hidden(X0,sK6)
      | ~ m1_subset_1(X0,sK4)
      | sK8 != X1 ) ),
    inference(superposition,[],[f49,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X1) = X0
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | k1_funct_1(X2,X1) != X0
        | ~ r2_hidden(X1,k1_relat_1(X2)) )
      & ( ( k1_funct_1(X2,X1) = X0
          & r2_hidden(X1,k1_relat_1(X2)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X1,X0,X2] :
      ( ( sP2(X1,X0,X2)
        | k1_funct_1(X2,X0) != X1
        | ~ r2_hidden(X0,k1_relat_1(X2)) )
      & ( ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) )
        | ~ sP2(X1,X0,X2) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X1,X0,X2] :
      ( ( sP2(X1,X0,X2)
        | k1_funct_1(X2,X0) != X1
        | ~ r2_hidden(X0,k1_relat_1(X2)) )
      & ( ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) )
        | ~ sP2(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( sP2(X1,X0,X2)
    <=> ( k1_funct_1(X2,X0) = X1
        & r2_hidden(X0,k1_relat_1(X2)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f49,plain,(
    ! [X5] :
      ( k1_funct_1(sK7,X5) != sK8
      | ~ r2_hidden(X5,sK6)
      | ~ m1_subset_1(X5,sK4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ! [X5] :
        ( k1_funct_1(sK7,X5) != sK8
        | ~ r2_hidden(X5,sK6)
        | ~ m1_subset_1(X5,sK4) )
    & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK7,sK4,sK5)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f13,f30,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK7,X5) != X4
              | ~ r2_hidden(X5,sK6)
              | ~ m1_subset_1(X5,sK4) )
          & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6)) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK7,sK4,sK5)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X4] :
        ( ! [X5] :
            ( k1_funct_1(sK7,X5) != X4
            | ~ r2_hidden(X5,sK6)
            | ~ m1_subset_1(X5,sK4) )
        & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6)) )
   => ( ! [X5] :
          ( k1_funct_1(sK7,X5) != sK8
          | ~ r2_hidden(X5,sK6)
          | ~ m1_subset_1(X5,sK4) )
      & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

fof(f375,plain,
    ( sP2(sK8,sK9(sK6,sK7,sK8),sK7)
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f373])).

fof(f373,plain,
    ( spl10_27
  <=> sP2(sK8,sK9(sK6,sK7,sK8),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f384,plain,
    ( spl10_27
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f383,f323,f109,f90,f373])).

fof(f90,plain,
    ( spl10_4
  <=> v1_funct_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f109,plain,
    ( spl10_6
  <=> v1_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f323,plain,
    ( spl10_22
  <=> r2_hidden(k4_tarski(sK9(sK6,sK7,sK8),sK8),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f383,plain,
    ( sP2(sK8,sK9(sK6,sK7,sK8),sK7)
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f363,f118])).

fof(f118,plain,
    ( ! [X0,X1] : sP3(sK7,X0,X1)
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(unit_resulting_resolution,[],[f111,f92,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( sP3(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f19,f27,f26])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> sP2(X1,X0,X2) )
      | ~ sP3(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f92,plain,
    ( v1_funct_1(sK7)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f111,plain,
    ( v1_relat_1(sK7)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f363,plain,
    ( sP2(sK8,sK9(sK6,sK7,sK8),sK7)
    | ~ sP3(sK7,sK9(sK6,sK7,sK8),sK8)
    | ~ spl10_22 ),
    inference(resolution,[],[f325,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),X0)
      | sP2(X2,X1,X0)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X1,X2),X0)
          | ~ sP2(X2,X1,X0) )
        & ( sP2(X2,X1,X0)
          | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ sP2(X1,X0,X2) )
        & ( sP2(X1,X0,X2)
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ sP3(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f325,plain,
    ( r2_hidden(k4_tarski(sK9(sK6,sK7,sK8),sK8),sK7)
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f323])).

fof(f332,plain,
    ( spl10_20
    | ~ spl10_9
    | ~ spl10_19 ),
    inference(avatar_split_clause,[],[f306,f300,f142,f313])).

fof(f142,plain,
    ( spl10_9
  <=> m1_subset_1(k1_relat_1(sK7),k1_zfmisc_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f300,plain,
    ( spl10_19
  <=> sP0(sK6,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f306,plain,
    ( m1_subset_1(sK9(sK6,sK7,sK8),sK4)
    | ~ spl10_9
    | ~ spl10_19 ),
    inference(unit_resulting_resolution,[],[f302,f253])).

fof(f253,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK9(X0,sK7,X1),sK4)
        | ~ sP0(X0,sK7,X1) )
    | ~ spl10_9 ),
    inference(resolution,[],[f58,f242])).

fof(f242,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(sK7))
        | m1_subset_1(X4,sK4) )
    | ~ spl10_9 ),
    inference(resolution,[],[f71,f144])).

fof(f144,plain,
    ( m1_subset_1(k1_relat_1(sK7),k1_zfmisc_1(sK4))
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f142])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),k1_relat_1(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(k4_tarski(X3,X2),X1)
            | ~ r2_hidden(X3,k1_relat_1(X1)) ) )
      & ( ( r2_hidden(sK9(X0,X1,X2),X0)
          & r2_hidden(k4_tarski(sK9(X0,X1,X2),X2),X1)
          & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(k4_tarski(X4,X2),X1)
          & r2_hidden(X4,k1_relat_1(X1)) )
     => ( r2_hidden(sK9(X0,X1,X2),X0)
        & r2_hidden(k4_tarski(sK9(X0,X1,X2),X2),X1)
        & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(k4_tarski(X3,X2),X1)
            | ~ r2_hidden(X3,k1_relat_1(X1)) ) )
      & ( ? [X4] :
            ( r2_hidden(X4,X0)
            & r2_hidden(k4_tarski(X4,X2),X1)
            & r2_hidden(X4,k1_relat_1(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X0),X2)
            | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(k4_tarski(X3,X0),X2)
          & r2_hidden(X3,k1_relat_1(X2)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f302,plain,
    ( sP0(sK6,sK7,sK8)
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f300])).

fof(f326,plain,
    ( spl10_22
    | ~ spl10_19 ),
    inference(avatar_split_clause,[],[f309,f300,f323])).

fof(f309,plain,
    ( r2_hidden(k4_tarski(sK9(sK6,sK7,sK8),sK8),sK7)
    | ~ spl10_19 ),
    inference(unit_resulting_resolution,[],[f302,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK9(X0,X1,X2),X2),X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f321,plain,
    ( spl10_21
    | ~ spl10_19 ),
    inference(avatar_split_clause,[],[f310,f300,f318])).

fof(f310,plain,
    ( r2_hidden(sK9(sK6,sK7,sK8),sK6)
    | ~ spl10_19 ),
    inference(unit_resulting_resolution,[],[f302,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f305,plain,
    ( spl10_19
    | ~ spl10_6
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f304,f290,f109,f300])).

fof(f290,plain,
    ( spl10_18
  <=> r2_hidden(sK8,k9_relat_1(sK7,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f304,plain,
    ( sP0(sK6,sK7,sK8)
    | ~ spl10_6
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f297,f115])).

fof(f115,plain,
    ( ! [X0,X1] : sP1(X0,sK7,X1)
    | ~ spl10_6 ),
    inference(unit_resulting_resolution,[],[f111,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f16,f24,f23])).

fof(f24,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f297,plain,
    ( sP0(sK6,sK7,sK8)
    | ~ sP1(sK8,sK7,sK6)
    | ~ spl10_18 ),
    inference(resolution,[],[f292,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
      | sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X1,X2))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X0,k9_relat_1(X1,X2)) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f292,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6))
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f290])).

fof(f295,plain,
    ( spl10_18
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f294,f80,f75,f290])).

fof(f75,plain,
    ( spl10_1
  <=> r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f80,plain,
    ( spl10_2
  <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f294,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6))
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f286,f82])).

fof(f82,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f286,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ spl10_1 ),
    inference(superposition,[],[f77,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f77,plain,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f145,plain,
    ( spl10_9
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f138,f133,f142])).

fof(f133,plain,
    ( spl10_8
  <=> r1_tarski(k1_relat_1(sK7),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f138,plain,
    ( m1_subset_1(k1_relat_1(sK7),k1_zfmisc_1(sK4))
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f135,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f135,plain,
    ( r1_tarski(k1_relat_1(sK7),sK4)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f133])).

fof(f136,plain,
    ( spl10_8
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f131,f126,f109,f133])).

fof(f126,plain,
    ( spl10_7
  <=> v4_relat_1(sK7,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f131,plain,
    ( r1_tarski(k1_relat_1(sK7),sK4)
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f111,f128,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f128,plain,
    ( v4_relat_1(sK7,sK4)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f126])).

fof(f130,plain,
    ( spl10_7
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f123,f80,f126])).

fof(f123,plain,
    ( v4_relat_1(sK7,sK4)
    | ~ spl10_2 ),
    inference(resolution,[],[f63,f82])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f114,plain,
    ( spl10_6
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f113,f80,f109])).

fof(f113,plain,
    ( v1_relat_1(sK7)
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f106,f51])).

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f106,plain,
    ( v1_relat_1(sK7)
    | ~ v1_relat_1(k2_zfmisc_1(sK4,sK5))
    | ~ spl10_2 ),
    inference(resolution,[],[f50,f82])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f93,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f45,f90])).

fof(f45,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f31])).

fof(f83,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f47,f80])).

fof(f47,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f48,f75])).

fof(f48,plain,(
    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:49:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.47  % (17317)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (17314)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.48  % (17327)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.48  % (17328)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.48  % (17330)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.48  % (17311)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (17327)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f437,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f78,f83,f93,f114,f130,f136,f145,f295,f305,f321,f326,f332,f384,f436])).
% 0.22/0.48  fof(f436,plain,(
% 0.22/0.48    ~spl10_20 | ~spl10_21 | ~spl10_27),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f435])).
% 0.22/0.48  fof(f435,plain,(
% 0.22/0.48    $false | (~spl10_20 | ~spl10_21 | ~spl10_27)),
% 0.22/0.48    inference(subsumption_resolution,[],[f434,f315])).
% 0.22/0.48  fof(f315,plain,(
% 0.22/0.48    m1_subset_1(sK9(sK6,sK7,sK8),sK4) | ~spl10_20),
% 0.22/0.48    inference(avatar_component_clause,[],[f313])).
% 0.22/0.48  fof(f313,plain,(
% 0.22/0.48    spl10_20 <=> m1_subset_1(sK9(sK6,sK7,sK8),sK4)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).
% 0.22/0.48  fof(f434,plain,(
% 0.22/0.48    ~m1_subset_1(sK9(sK6,sK7,sK8),sK4) | (~spl10_21 | ~spl10_27)),
% 0.22/0.48    inference(subsumption_resolution,[],[f429,f320])).
% 0.22/0.48  fof(f320,plain,(
% 0.22/0.48    r2_hidden(sK9(sK6,sK7,sK8),sK6) | ~spl10_21),
% 0.22/0.48    inference(avatar_component_clause,[],[f318])).
% 0.22/0.48  fof(f318,plain,(
% 0.22/0.48    spl10_21 <=> r2_hidden(sK9(sK6,sK7,sK8),sK6)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 0.22/0.48  fof(f429,plain,(
% 0.22/0.48    ~r2_hidden(sK9(sK6,sK7,sK8),sK6) | ~m1_subset_1(sK9(sK6,sK7,sK8),sK4) | ~spl10_27),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f426])).
% 0.22/0.48  fof(f426,plain,(
% 0.22/0.48    ~r2_hidden(sK9(sK6,sK7,sK8),sK6) | ~m1_subset_1(sK9(sK6,sK7,sK8),sK4) | sK8 != sK8 | ~spl10_27),
% 0.22/0.48    inference(resolution,[],[f375,f214])).
% 0.22/0.48  fof(f214,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~sP2(X1,X0,sK7) | ~r2_hidden(X0,sK6) | ~m1_subset_1(X0,sK4) | sK8 != X1) )),
% 0.22/0.48    inference(superposition,[],[f49,f68])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k1_funct_1(X2,X1) = X0 | ~sP2(X0,X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f44])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | k1_funct_1(X2,X1) != X0 | ~r2_hidden(X1,k1_relat_1(X2))) & ((k1_funct_1(X2,X1) = X0 & r2_hidden(X1,k1_relat_1(X2))) | ~sP2(X0,X1,X2)))),
% 0.22/0.48    inference(rectify,[],[f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~sP2(X1,X0,X2)))),
% 0.22/0.48    inference(flattening,[],[f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~sP2(X1,X0,X2)))),
% 0.22/0.48    inference(nnf_transformation,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ! [X1,X0,X2] : (sP2(X1,X0,X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))))),
% 0.22/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,sK4)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    (! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,sK4)) & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f13,f30,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK7,X5) != X4 | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,sK4)) & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ? [X4] : (! [X5] : (k1_funct_1(sK7,X5) != X4 | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,sK4)) & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6))) => (! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,sK4)) & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.48    inference(flattening,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.48    inference(ennf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.48    inference(negated_conjecture,[],[f10])).
% 0.22/0.48  fof(f10,conjecture,(
% 0.22/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).
% 0.22/0.48  fof(f375,plain,(
% 0.22/0.48    sP2(sK8,sK9(sK6,sK7,sK8),sK7) | ~spl10_27),
% 0.22/0.48    inference(avatar_component_clause,[],[f373])).
% 0.22/0.48  fof(f373,plain,(
% 0.22/0.48    spl10_27 <=> sP2(sK8,sK9(sK6,sK7,sK8),sK7)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).
% 0.22/0.48  fof(f384,plain,(
% 0.22/0.48    spl10_27 | ~spl10_4 | ~spl10_6 | ~spl10_22),
% 0.22/0.48    inference(avatar_split_clause,[],[f383,f323,f109,f90,f373])).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    spl10_4 <=> v1_funct_1(sK7)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.22/0.48  fof(f109,plain,(
% 0.22/0.48    spl10_6 <=> v1_relat_1(sK7)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.22/0.48  fof(f323,plain,(
% 0.22/0.48    spl10_22 <=> r2_hidden(k4_tarski(sK9(sK6,sK7,sK8),sK8),sK7)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).
% 0.22/0.48  fof(f383,plain,(
% 0.22/0.48    sP2(sK8,sK9(sK6,sK7,sK8),sK7) | (~spl10_4 | ~spl10_6 | ~spl10_22)),
% 0.22/0.48    inference(subsumption_resolution,[],[f363,f118])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    ( ! [X0,X1] : (sP3(sK7,X0,X1)) ) | (~spl10_4 | ~spl10_6)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f111,f92,f70])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (sP3(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (sP3(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(definition_folding,[],[f19,f27,f26])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X2,X0,X1] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> sP2(X1,X0,X2)) | ~sP3(X2,X0,X1))),
% 0.22/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(flattening,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    v1_funct_1(sK7) | ~spl10_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f90])).
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    v1_relat_1(sK7) | ~spl10_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f109])).
% 0.22/0.48  fof(f363,plain,(
% 0.22/0.48    sP2(sK8,sK9(sK6,sK7,sK8),sK7) | ~sP3(sK7,sK9(sK6,sK7,sK8),sK8) | ~spl10_22),
% 0.22/0.48    inference(resolution,[],[f325,f65])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X1,X2),X0) | sP2(X2,X1,X0) | ~sP3(X0,X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X1,X2),X0) | ~sP2(X2,X1,X0)) & (sP2(X2,X1,X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~sP3(X0,X1,X2))),
% 0.22/0.48    inference(rectify,[],[f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ! [X2,X0,X1] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~sP2(X1,X0,X2)) & (sP2(X1,X0,X2) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~sP3(X2,X0,X1))),
% 0.22/0.48    inference(nnf_transformation,[],[f27])).
% 0.22/0.48  fof(f325,plain,(
% 0.22/0.48    r2_hidden(k4_tarski(sK9(sK6,sK7,sK8),sK8),sK7) | ~spl10_22),
% 0.22/0.48    inference(avatar_component_clause,[],[f323])).
% 0.22/0.48  fof(f332,plain,(
% 0.22/0.48    spl10_20 | ~spl10_9 | ~spl10_19),
% 0.22/0.48    inference(avatar_split_clause,[],[f306,f300,f142,f313])).
% 0.22/0.48  fof(f142,plain,(
% 0.22/0.48    spl10_9 <=> m1_subset_1(k1_relat_1(sK7),k1_zfmisc_1(sK4))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.22/0.48  fof(f300,plain,(
% 0.22/0.48    spl10_19 <=> sP0(sK6,sK7,sK8)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 0.22/0.48  fof(f306,plain,(
% 0.22/0.48    m1_subset_1(sK9(sK6,sK7,sK8),sK4) | (~spl10_9 | ~spl10_19)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f302,f253])).
% 0.22/0.48  fof(f253,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_subset_1(sK9(X0,sK7,X1),sK4) | ~sP0(X0,sK7,X1)) ) | ~spl10_9),
% 0.22/0.48    inference(resolution,[],[f58,f242])).
% 0.22/0.48  fof(f242,plain,(
% 0.22/0.48    ( ! [X4] : (~r2_hidden(X4,k1_relat_1(sK7)) | m1_subset_1(X4,sK4)) ) | ~spl10_9),
% 0.22/0.48    inference(resolution,[],[f71,f144])).
% 0.22/0.48  fof(f144,plain,(
% 0.22/0.48    m1_subset_1(k1_relat_1(sK7),k1_zfmisc_1(sK4)) | ~spl10_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f142])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.48    inference(flattening,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X1,X2),k1_relat_1(X1)) | ~sP0(X0,X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(k4_tarski(X3,X2),X1) | ~r2_hidden(X3,k1_relat_1(X1)))) & ((r2_hidden(sK9(X0,X1,X2),X0) & r2_hidden(k4_tarski(sK9(X0,X1,X2),X2),X1) & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X1))) | ~sP0(X0,X1,X2)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f37,f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X2),X1) & r2_hidden(X4,k1_relat_1(X1))) => (r2_hidden(sK9(X0,X1,X2),X0) & r2_hidden(k4_tarski(sK9(X0,X1,X2),X2),X1) & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X1))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(k4_tarski(X3,X2),X1) | ~r2_hidden(X3,k1_relat_1(X1)))) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X2),X1) & r2_hidden(X4,k1_relat_1(X1))) | ~sP0(X0,X1,X2)))),
% 0.22/0.48    inference(rectify,[],[f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~sP0(X1,X2,X0)))),
% 0.22/0.48    inference(nnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))))),
% 0.22/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.48  fof(f302,plain,(
% 0.22/0.48    sP0(sK6,sK7,sK8) | ~spl10_19),
% 0.22/0.48    inference(avatar_component_clause,[],[f300])).
% 0.22/0.48  fof(f326,plain,(
% 0.22/0.48    spl10_22 | ~spl10_19),
% 0.22/0.48    inference(avatar_split_clause,[],[f309,f300,f323])).
% 0.22/0.48  fof(f309,plain,(
% 0.22/0.48    r2_hidden(k4_tarski(sK9(sK6,sK7,sK8),sK8),sK7) | ~spl10_19),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f302,f59])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK9(X0,X1,X2),X2),X1) | ~sP0(X0,X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f39])).
% 0.22/0.48  fof(f321,plain,(
% 0.22/0.48    spl10_21 | ~spl10_19),
% 0.22/0.48    inference(avatar_split_clause,[],[f310,f300,f318])).
% 0.22/0.48  fof(f310,plain,(
% 0.22/0.48    r2_hidden(sK9(sK6,sK7,sK8),sK6) | ~spl10_19),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f302,f60])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X1,X2),X0) | ~sP0(X0,X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f39])).
% 0.22/0.48  fof(f305,plain,(
% 0.22/0.48    spl10_19 | ~spl10_6 | ~spl10_18),
% 0.22/0.48    inference(avatar_split_clause,[],[f304,f290,f109,f300])).
% 0.22/0.48  fof(f290,plain,(
% 0.22/0.48    spl10_18 <=> r2_hidden(sK8,k9_relat_1(sK7,sK6))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 0.22/0.48  fof(f304,plain,(
% 0.22/0.48    sP0(sK6,sK7,sK8) | (~spl10_6 | ~spl10_18)),
% 0.22/0.48    inference(subsumption_resolution,[],[f297,f115])).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    ( ! [X0,X1] : (sP1(X0,sK7,X1)) ) | ~spl10_6),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f111,f62])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (sP1(X0,X2,X1) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(definition_folding,[],[f16,f24,f23])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X0,X2,X1] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 0.22/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.22/0.48  fof(f297,plain,(
% 0.22/0.48    sP0(sK6,sK7,sK8) | ~sP1(sK8,sK7,sK6) | ~spl10_18),
% 0.22/0.48    inference(resolution,[],[f292,f56])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X1,X2)) | sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X1,X2)) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X0,k9_relat_1(X1,X2)))) | ~sP1(X0,X1,X2))),
% 0.22/0.48    inference(rectify,[],[f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ! [X0,X2,X1] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~sP1(X0,X2,X1))),
% 0.22/0.48    inference(nnf_transformation,[],[f24])).
% 0.22/0.48  fof(f292,plain,(
% 0.22/0.48    r2_hidden(sK8,k9_relat_1(sK7,sK6)) | ~spl10_18),
% 0.22/0.48    inference(avatar_component_clause,[],[f290])).
% 0.22/0.48  fof(f295,plain,(
% 0.22/0.48    spl10_18 | ~spl10_1 | ~spl10_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f294,f80,f75,f290])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    spl10_1 <=> r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    spl10_2 <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.22/0.48  fof(f294,plain,(
% 0.22/0.48    r2_hidden(sK8,k9_relat_1(sK7,sK6)) | (~spl10_1 | ~spl10_2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f286,f82])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~spl10_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f80])).
% 0.22/0.48  fof(f286,plain,(
% 0.22/0.48    r2_hidden(sK8,k9_relat_1(sK7,sK6)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~spl10_1),
% 0.22/0.48    inference(superposition,[],[f77,f72])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) | ~spl10_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f75])).
% 0.22/0.48  fof(f145,plain,(
% 0.22/0.48    spl10_9 | ~spl10_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f138,f133,f142])).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    spl10_8 <=> r1_tarski(k1_relat_1(sK7),sK4)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.22/0.48  fof(f138,plain,(
% 0.22/0.48    m1_subset_1(k1_relat_1(sK7),k1_zfmisc_1(sK4)) | ~spl10_8),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f135,f55])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.48    inference(nnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.48  fof(f135,plain,(
% 0.22/0.48    r1_tarski(k1_relat_1(sK7),sK4) | ~spl10_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f133])).
% 0.22/0.48  fof(f136,plain,(
% 0.22/0.48    spl10_8 | ~spl10_6 | ~spl10_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f131,f126,f109,f133])).
% 0.22/0.48  fof(f126,plain,(
% 0.22/0.48    spl10_7 <=> v4_relat_1(sK7,sK4)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    r1_tarski(k1_relat_1(sK7),sK4) | (~spl10_6 | ~spl10_7)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f111,f128,f52])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(nnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.22/0.48  fof(f128,plain,(
% 0.22/0.48    v4_relat_1(sK7,sK4) | ~spl10_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f126])).
% 0.22/0.48  fof(f130,plain,(
% 0.22/0.48    spl10_7 | ~spl10_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f123,f80,f126])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    v4_relat_1(sK7,sK4) | ~spl10_2),
% 0.22/0.48    inference(resolution,[],[f63,f82])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.48  fof(f114,plain,(
% 0.22/0.48    spl10_6 | ~spl10_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f113,f80,f109])).
% 0.22/0.48  fof(f113,plain,(
% 0.22/0.48    v1_relat_1(sK7) | ~spl10_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f106,f51])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    v1_relat_1(sK7) | ~v1_relat_1(k2_zfmisc_1(sK4,sK5)) | ~spl10_2),
% 0.22/0.48    inference(resolution,[],[f50,f82])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    spl10_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f45,f90])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    v1_funct_1(sK7)),
% 0.22/0.48    inference(cnf_transformation,[],[f31])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    spl10_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f47,f80])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 0.22/0.48    inference(cnf_transformation,[],[f31])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    spl10_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f48,f75])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))),
% 0.22/0.48    inference(cnf_transformation,[],[f31])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (17327)------------------------------
% 0.22/0.48  % (17327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (17327)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (17327)Memory used [KB]: 11001
% 0.22/0.48  % (17327)Time elapsed: 0.075 s
% 0.22/0.48  % (17327)------------------------------
% 0.22/0.48  % (17327)------------------------------
% 0.22/0.49  % (17309)Success in time 0.128 s
%------------------------------------------------------------------------------
