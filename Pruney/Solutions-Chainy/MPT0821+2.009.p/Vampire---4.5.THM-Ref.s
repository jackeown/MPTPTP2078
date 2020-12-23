%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 176 expanded)
%              Number of leaves         :   20 (  61 expanded)
%              Depth                    :   14
%              Number of atoms          :  274 ( 743 expanded)
%              Number of equality atoms :   45 ( 155 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f166,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f65,f70,f98,f123,f138,f165])).

fof(f165,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f64,f162])).

fof(f162,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(backward_demodulation,[],[f143,f160])).

fof(f160,plain,
    ( sK1 = k1_relat_1(sK2)
    | ~ spl9_2 ),
    inference(forward_demodulation,[],[f71,f69])).

fof(f69,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK2)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl9_2
  <=> sK1 = k1_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f71,plain,(
    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f33,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( sK1 != k1_relset_1(sK1,sK0,sK2)
      | ( ! [X4] : ~ r2_hidden(k4_tarski(sK3,X4),sK2)
        & r2_hidden(sK3,sK1) ) )
    & ( sK1 = k1_relset_1(sK1,sK0,sK2)
      | ! [X5] :
          ( r2_hidden(k4_tarski(X5,sK4(X5)),sK2)
          | ~ r2_hidden(X5,sK1) ) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X1,X0,X2) != X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) ) )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ! [X5] :
              ( ? [X6] : r2_hidden(k4_tarski(X5,X6),X2)
              | ~ r2_hidden(X5,X1) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( sK1 != k1_relset_1(sK1,sK0,sK2)
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),sK2)
            & r2_hidden(X3,sK1) ) )
      & ( sK1 = k1_relset_1(sK1,sK0,sK2)
        | ! [X5] :
            ( ? [X6] : r2_hidden(k4_tarski(X5,X6),sK2)
            | ~ r2_hidden(X5,sK1) ) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X3] :
        ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),sK2)
        & r2_hidden(X3,sK1) )
   => ( ! [X4] : ~ r2_hidden(k4_tarski(sK3,X4),sK2)
      & r2_hidden(sK3,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X5] :
      ( ? [X6] : r2_hidden(k4_tarski(X5,X6),sK2)
     => r2_hidden(k4_tarski(X5,sK4(X5)),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
            & r2_hidden(X3,X1) ) )
      & ( k1_relset_1(X1,X0,X2) = X1
        | ! [X5] :
            ( ? [X6] : r2_hidden(k4_tarski(X5,X6),X2)
            | ~ r2_hidden(X5,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
            & r2_hidden(X3,X1) ) )
      & ( k1_relset_1(X1,X0,X2) = X1
        | ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
            & r2_hidden(X3,X1) ) )
      & ( k1_relset_1(X1,X0,X2) = X1
        | ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <~> k1_relset_1(X1,X0,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( ! [X3] :
              ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
                & r2_hidden(X3,X1) )
        <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

fof(f143,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl9_1 ),
    inference(resolution,[],[f57,f54])).

fof(f54,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f27,f30,f29,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f57,plain,
    ( ! [X4] : ~ r2_hidden(k4_tarski(sK3,X4),sK2)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl9_1
  <=> ! [X4] : ~ r2_hidden(k4_tarski(sK3,X4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f64,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl9_3
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f138,plain,
    ( spl9_2
    | ~ spl9_8 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | spl9_2
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f83,f97])).

fof(f97,plain,
    ( sK1 = k1_relat_1(sK2)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl9_8
  <=> sK1 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f83,plain,
    ( sK1 != k1_relat_1(sK2)
    | spl9_2 ),
    inference(superposition,[],[f60,f71])).

fof(f60,plain,
    ( sK1 != k1_relset_1(sK1,sK0,sK2)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f123,plain,
    ( ~ spl9_4
    | spl9_7 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | ~ spl9_4
    | spl9_7 ),
    inference(subsumption_resolution,[],[f101,f94])).

fof(f94,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK2))
    | spl9_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl9_7
  <=> r1_tarski(sK1,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f101,plain,
    ( r1_tarski(sK1,k1_relat_1(sK2))
    | ~ spl9_4 ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,
    ( r1_tarski(sK1,k1_relat_1(sK2))
    | r1_tarski(sK1,k1_relat_1(sK2))
    | ~ spl9_4 ),
    inference(resolution,[],[f86,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f86,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(X0,k1_relat_1(sK2)),sK1)
        | r1_tarski(X0,k1_relat_1(sK2)) )
    | ~ spl9_4 ),
    inference(resolution,[],[f82,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f82,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k1_relat_1(sK2))
        | ~ r2_hidden(X1,sK1) )
    | ~ spl9_4 ),
    inference(resolution,[],[f68,f53])).

fof(f53,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f68,plain,
    ( ! [X5] :
        ( r2_hidden(k4_tarski(X5,sK4(X5)),sK2)
        | ~ r2_hidden(X5,sK1) )
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl9_4
  <=> ! [X5] :
        ( r2_hidden(k4_tarski(X5,sK4(X5)),sK2)
        | ~ r2_hidden(X5,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f98,plain,
    ( ~ spl9_7
    | spl9_8 ),
    inference(avatar_split_clause,[],[f91,f96,f93])).

fof(f91,plain,
    ( sK1 = k1_relat_1(sK2)
    | ~ r1_tarski(sK1,k1_relat_1(sK2)) ),
    inference(resolution,[],[f90,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f90,plain,(
    r1_tarski(k1_relat_1(sK2),sK1) ),
    inference(resolution,[],[f85,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f85,plain,(
    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(global_subsumption,[],[f33,f84])).

fof(f84,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f50,f71])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f70,plain,
    ( spl9_4
    | spl9_2 ),
    inference(avatar_split_clause,[],[f34,f59,f67])).

fof(f34,plain,(
    ! [X5] :
      ( sK1 = k1_relset_1(sK1,sK0,sK2)
      | r2_hidden(k4_tarski(X5,sK4(X5)),sK2)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,
    ( spl9_3
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f35,f59,f63])).

fof(f35,plain,
    ( sK1 != k1_relset_1(sK1,sK0,sK2)
    | r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,
    ( spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f36,f59,f56])).

fof(f36,plain,(
    ! [X4] :
      ( sK1 != k1_relset_1(sK1,sK0,sK2)
      | ~ r2_hidden(k4_tarski(sK3,X4),sK2) ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:55:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (18637)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (18655)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (18639)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (18643)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (18639)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f61,f65,f70,f98,f123,f138,f165])).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    ~spl9_1 | ~spl9_2 | ~spl9_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f163])).
% 0.21/0.53  fof(f163,plain,(
% 0.21/0.53    $false | (~spl9_1 | ~spl9_2 | ~spl9_3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f64,f162])).
% 0.21/0.53  fof(f162,plain,(
% 0.21/0.53    ~r2_hidden(sK3,sK1) | (~spl9_1 | ~spl9_2)),
% 0.21/0.53    inference(backward_demodulation,[],[f143,f160])).
% 0.21/0.53  fof(f160,plain,(
% 0.21/0.53    sK1 = k1_relat_1(sK2) | ~spl9_2),
% 0.21/0.53    inference(forward_demodulation,[],[f71,f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    sK1 = k1_relset_1(sK1,sK0,sK2) | ~spl9_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    spl9_2 <=> sK1 = k1_relset_1(sK1,sK0,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 0.21/0.53    inference(resolution,[],[f33,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    (sK1 != k1_relset_1(sK1,sK0,sK2) | (! [X4] : ~r2_hidden(k4_tarski(sK3,X4),sK2) & r2_hidden(sK3,sK1))) & (sK1 = k1_relset_1(sK1,sK0,sK2) | ! [X5] : (r2_hidden(k4_tarski(X5,sK4(X5)),sK2) | ~r2_hidden(X5,sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f18,f17,f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1))) & (k1_relset_1(X1,X0,X2) = X1 | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(X5,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((sK1 != k1_relset_1(sK1,sK0,sK2) | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),sK2) & r2_hidden(X3,sK1))) & (sK1 = k1_relset_1(sK1,sK0,sK2) | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X5,X6),sK2) | ~r2_hidden(X5,sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),sK2) & r2_hidden(X3,sK1)) => (! [X4] : ~r2_hidden(k4_tarski(sK3,X4),sK2) & r2_hidden(sK3,sK1))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X5] : (? [X6] : r2_hidden(k4_tarski(X5,X6),sK2) => r2_hidden(k4_tarski(X5,sK4(X5)),sK2))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1))) & (k1_relset_1(X1,X0,X2) = X1 | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(X5,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.53    inference(rectify,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1))) & (k1_relset_1(X1,X0,X2) = X1 | ! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.53    inference(flattening,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (((k1_relset_1(X1,X0,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1))) & (k1_relset_1(X1,X0,X2) = X1 | ! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.53    inference(nnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ? [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <~> k1_relset_1(X1,X0,X2) = X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.21/0.53    inference(negated_conjecture,[],[f7])).
% 0.21/0.53  fof(f7,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    ~r2_hidden(sK3,k1_relat_1(sK2)) | ~spl9_1),
% 0.21/0.53    inference(resolution,[],[f57,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 0.21/0.53    inference(equality_resolution,[],[f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f27,f30,f29,f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.53    inference(rectify,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X4] : (~r2_hidden(k4_tarski(sK3,X4),sK2)) ) | ~spl9_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    spl9_1 <=> ! [X4] : ~r2_hidden(k4_tarski(sK3,X4),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    r2_hidden(sK3,sK1) | ~spl9_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    spl9_3 <=> r2_hidden(sK3,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    spl9_2 | ~spl9_8),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f126])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    $false | (spl9_2 | ~spl9_8)),
% 0.21/0.53    inference(subsumption_resolution,[],[f83,f97])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    sK1 = k1_relat_1(sK2) | ~spl9_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f96])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    spl9_8 <=> sK1 = k1_relat_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    sK1 != k1_relat_1(sK2) | spl9_2),
% 0.21/0.53    inference(superposition,[],[f60,f71])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    sK1 != k1_relset_1(sK1,sK0,sK2) | spl9_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f59])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    ~spl9_4 | spl9_7),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f122])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    $false | (~spl9_4 | spl9_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f101,f94])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    ~r1_tarski(sK1,k1_relat_1(sK2)) | spl9_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f93])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    spl9_7 <=> r1_tarski(sK1,k1_relat_1(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    r1_tarski(sK1,k1_relat_1(sK2)) | ~spl9_4),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f99])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    r1_tarski(sK1,k1_relat_1(sK2)) | r1_tarski(sK1,k1_relat_1(sK2)) | ~spl9_4),
% 0.21/0.53    inference(resolution,[],[f86,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(rectify,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK5(X0,k1_relat_1(sK2)),sK1) | r1_tarski(X0,k1_relat_1(sK2))) ) | ~spl9_4),
% 0.21/0.53    inference(resolution,[],[f82,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X1] : (r2_hidden(X1,k1_relat_1(sK2)) | ~r2_hidden(X1,sK1)) ) | ~spl9_4),
% 0.21/0.53    inference(resolution,[],[f68,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 0.21/0.53    inference(equality_resolution,[],[f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X5] : (r2_hidden(k4_tarski(X5,sK4(X5)),sK2) | ~r2_hidden(X5,sK1)) ) | ~spl9_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    spl9_4 <=> ! [X5] : (r2_hidden(k4_tarski(X5,sK4(X5)),sK2) | ~r2_hidden(X5,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ~spl9_7 | spl9_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f91,f96,f93])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    sK1 = k1_relat_1(sK2) | ~r1_tarski(sK1,k1_relat_1(sK2))),
% 0.21/0.53    inference(resolution,[],[f90,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    r1_tarski(k1_relat_1(sK2),sK1)),
% 0.21/0.53    inference(resolution,[],[f85,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.53    inference(nnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.21/0.53    inference(global_subsumption,[],[f33,f84])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.53    inference(superposition,[],[f50,f71])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    spl9_4 | spl9_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f34,f59,f67])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X5] : (sK1 = k1_relset_1(sK1,sK0,sK2) | r2_hidden(k4_tarski(X5,sK4(X5)),sK2) | ~r2_hidden(X5,sK1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    spl9_3 | ~spl9_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f35,f59,f63])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    sK1 != k1_relset_1(sK1,sK0,sK2) | r2_hidden(sK3,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    spl9_1 | ~spl9_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f36,f59,f56])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X4] : (sK1 != k1_relset_1(sK1,sK0,sK2) | ~r2_hidden(k4_tarski(sK3,X4),sK2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (18639)------------------------------
% 0.21/0.53  % (18639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (18639)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (18639)Memory used [KB]: 10746
% 0.21/0.53  % (18639)Time elapsed: 0.106 s
% 0.21/0.53  % (18639)------------------------------
% 0.21/0.53  % (18639)------------------------------
% 0.21/0.53  % (18663)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (18636)Success in time 0.166 s
%------------------------------------------------------------------------------
