%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 163 expanded)
%              Number of leaves         :   24 (  68 expanded)
%              Depth                    :   11
%              Number of atoms          :  349 ( 660 expanded)
%              Number of equality atoms :   73 ( 142 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f60,f64,f70,f75,f83,f89,f92,f97,f102,f110,f121,f126])).

fof(f126,plain,
    ( ~ spl7_7
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_9
    | spl7_13 ),
    inference(avatar_split_clause,[],[f123,f119,f95,f73,f62,f81])).

fof(f81,plain,
    ( spl7_7
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f62,plain,
    ( spl7_3
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f73,plain,
    ( spl7_5
  <=> r2_hidden(sK2,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f95,plain,
    ( spl7_9
  <=> k2_relat_1(sK3) = k9_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f119,plain,
    ( spl7_13
  <=> r2_hidden(sK6(sK3,sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f123,plain,
    ( ~ r2_hidden(sK2,k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_9
    | spl7_13 ),
    inference(forward_demodulation,[],[f122,f96])).

fof(f96,plain,
    ( k2_relat_1(sK3) = k9_relat_1(sK3,sK0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f95])).

fof(f122,plain,
    ( ~ r2_hidden(sK2,k9_relat_1(sK3,sK0))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl7_13 ),
    inference(resolution,[],[f120,f51])).

fof(f51,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK4(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK4(X0,X1,X2),X2) )
              & ( ( sK4(X0,X1,X2) = k1_funct_1(X0,sK5(X0,X1,X2))
                  & r2_hidden(sK5(X0,X1,X2),X1)
                  & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK6(X0,X1,X6)) = X6
                    & r2_hidden(sK6(X0,X1,X6),X1)
                    & r2_hidden(sK6(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f28,f27,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK4(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK4(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = sK4(X0,X1,X2)
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( sK4(X0,X1,X2) = k1_funct_1(X0,sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X1,X6)) = X6
        & r2_hidden(sK6(X0,X1,X6),X1)
        & r2_hidden(sK6(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(f120,plain,
    ( ~ r2_hidden(sK6(sK3,sK0,sK2),sK0)
    | spl7_13 ),
    inference(avatar_component_clause,[],[f119])).

fof(f121,plain,
    ( ~ spl7_13
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f117,f108,f119])).

fof(f108,plain,
    ( spl7_11
  <=> sK2 = k1_funct_1(sK3,sK6(sK3,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f117,plain,
    ( ~ r2_hidden(sK6(sK3,sK0,sK2),sK0)
    | ~ spl7_11 ),
    inference(trivial_inequality_removal,[],[f116])).

fof(f116,plain,
    ( sK2 != sK2
    | ~ r2_hidden(sK6(sK3,sK0,sK2),sK0)
    | ~ spl7_11 ),
    inference(superposition,[],[f33,f109])).

fof(f109,plain,
    ( sK2 = k1_funct_1(sK3,sK6(sK3,sK0,sK2))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f108])).

fof(f33,plain,(
    ! [X4] :
      ( sK2 != k1_funct_1(sK3,X4)
      | ~ r2_hidden(X4,sK0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ! [X4] :
        ( sK2 != k1_funct_1(sK3,X4)
        | ~ r2_hidden(X4,sK0) )
    & r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X2
            | ~ r2_hidden(X4,X0) )
        & r2_hidden(X2,k2_relset_1(X0,X1,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( sK2 != k1_funct_1(sK3,X4)
          | ~ r2_hidden(X4,sK0) )
      & r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ~ ( k1_funct_1(X3,X4) = X2
                  & r2_hidden(X4,X0) )
            & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ~ ( k1_funct_1(X3,X4) = X2
                  & r2_hidden(X4,X0) )
            & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ~ ( k1_funct_1(X3,X4) = X2
                & r2_hidden(X4,X0) )
          & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

fof(f110,plain,
    ( spl7_11
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f105,f100,f95,f73,f108])).

fof(f100,plain,
    ( spl7_10
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | k1_funct_1(sK3,sK6(sK3,X1,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f105,plain,
    ( sK2 = k1_funct_1(sK3,sK6(sK3,sK0,sK2))
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(resolution,[],[f104,f74])).

fof(f74,plain,
    ( r2_hidden(sK2,k2_relat_1(sK3))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | k1_funct_1(sK3,sK6(sK3,sK0,X0)) = X0 )
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(superposition,[],[f101,f96])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | k1_funct_1(sK3,sK6(sK3,X1,X0)) = X0 )
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f102,plain,
    ( ~ spl7_7
    | spl7_10
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f98,f62,f100,f81])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | k1_funct_1(sK3,sK6(sK3,X1,X0)) = X0
        | ~ v1_relat_1(sK3) )
    | ~ spl7_3 ),
    inference(resolution,[],[f50,f63])).

fof(f63,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f50,plain,(
    ! [X6,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | k1_funct_1(X0,sK6(X0,X1,X6)) = X6
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK6(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f97,plain,
    ( ~ spl7_7
    | spl7_9
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f93,f78,f95,f81])).

fof(f78,plain,
    ( spl7_6
  <=> sK3 = k7_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f93,plain,
    ( k2_relat_1(sK3) = k9_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl7_6 ),
    inference(superposition,[],[f44,f79])).

fof(f79,plain,
    ( sK3 = k7_relat_1(sK3,sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f92,plain,(
    spl7_8 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | spl7_8 ),
    inference(resolution,[],[f88,f43])).

fof(f43,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f88,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl7_8
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f89,plain,
    ( ~ spl7_8
    | ~ spl7_2
    | spl7_7 ),
    inference(avatar_split_clause,[],[f85,f81,f58,f87])).

fof(f58,plain,
    ( spl7_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f85,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl7_2
    | spl7_7 ),
    inference(resolution,[],[f84,f59])).

fof(f59,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f84,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl7_7 ),
    inference(resolution,[],[f82,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f82,plain,
    ( ~ v1_relat_1(sK3)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f83,plain,
    ( spl7_6
    | ~ spl7_7
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f76,f58,f81,f78])).

fof(f76,plain,
    ( ~ v1_relat_1(sK3)
    | sK3 = k7_relat_1(sK3,sK0)
    | ~ spl7_2 ),
    inference(resolution,[],[f65,f59])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = X0 ) ),
    inference(resolution,[],[f45,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f75,plain,
    ( spl7_5
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f71,f68,f54,f73])).

fof(f54,plain,
    ( spl7_1
  <=> r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f68,plain,
    ( spl7_4
  <=> k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f71,plain,
    ( r2_hidden(sK2,k2_relat_1(sK3))
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(superposition,[],[f55,f69])).

fof(f69,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f55,plain,
    ( r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f70,plain,
    ( spl7_4
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f66,f58,f68])).

fof(f66,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl7_2 ),
    inference(resolution,[],[f46,f59])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f64,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f30,f62])).

fof(f30,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f31,f58])).

fof(f31,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f32,f54])).

fof(f32,plain,(
    r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:42:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (31150)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.47  % (31146)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (31143)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (31142)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.47  % (31150)Refutation not found, incomplete strategy% (31150)------------------------------
% 0.20/0.47  % (31150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (31150)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (31150)Memory used [KB]: 6140
% 0.20/0.47  % (31150)Time elapsed: 0.061 s
% 0.20/0.47  % (31150)------------------------------
% 0.20/0.47  % (31150)------------------------------
% 0.20/0.47  % (31146)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (31151)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f56,f60,f64,f70,f75,f83,f89,f92,f97,f102,f110,f121,f126])).
% 0.20/0.47  fof(f126,plain,(
% 0.20/0.47    ~spl7_7 | ~spl7_3 | ~spl7_5 | ~spl7_9 | spl7_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f123,f119,f95,f73,f62,f81])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    spl7_7 <=> v1_relat_1(sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    spl7_3 <=> v1_funct_1(sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    spl7_5 <=> r2_hidden(sK2,k2_relat_1(sK3))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    spl7_9 <=> k2_relat_1(sK3) = k9_relat_1(sK3,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    spl7_13 <=> r2_hidden(sK6(sK3,sK0,sK2),sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    ~r2_hidden(sK2,k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl7_9 | spl7_13)),
% 0.20/0.47    inference(forward_demodulation,[],[f122,f96])).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    k2_relat_1(sK3) = k9_relat_1(sK3,sK0) | ~spl7_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f95])).
% 0.20/0.47  fof(f122,plain,(
% 0.20/0.47    ~r2_hidden(sK2,k9_relat_1(sK3,sK0)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl7_13),
% 0.20/0.47    inference(resolution,[],[f120,f51])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X6,X0,X1] : (r2_hidden(sK6(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(equality_resolution,[],[f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X6,X2,X0,X1] : (r2_hidden(sK6(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK4(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((sK4(X0,X1,X2) = k1_funct_1(X0,sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK6(X0,X1,X6)) = X6 & r2_hidden(sK6(X0,X1,X6),X1) & r2_hidden(sK6(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f28,f27,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK4(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK4(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = sK4(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (sK4(X0,X1,X2) = k1_funct_1(X0,sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X1,X6)) = X6 & r2_hidden(sK6(X0,X1,X6),X1) & r2_hidden(sK6(X0,X1,X6),k1_relat_1(X0))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(rectify,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    ~r2_hidden(sK6(sK3,sK0,sK2),sK0) | spl7_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f119])).
% 0.20/0.47  fof(f121,plain,(
% 0.20/0.47    ~spl7_13 | ~spl7_11),
% 0.20/0.47    inference(avatar_split_clause,[],[f117,f108,f119])).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    spl7_11 <=> sK2 = k1_funct_1(sK3,sK6(sK3,sK0,sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    ~r2_hidden(sK6(sK3,sK0,sK2),sK0) | ~spl7_11),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f116])).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    sK2 != sK2 | ~r2_hidden(sK6(sK3,sK0,sK2),sK0) | ~spl7_11),
% 0.20/0.47    inference(superposition,[],[f33,f109])).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    sK2 = k1_funct_1(sK3,sK6(sK3,sK0,sK2)) | ~spl7_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f108])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X4] : (sK2 != k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X4] : (sK2 != k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (! [X4] : (sK2 != k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 0.20/0.47    inference(flattening,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 0.20/0.47    inference(pure_predicate_removal,[],[f9])).
% 0.20/0.47  fof(f9,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 0.20/0.47    inference(negated_conjecture,[],[f8])).
% 0.20/0.47  fof(f8,conjecture,(
% 0.20/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    spl7_11 | ~spl7_5 | ~spl7_9 | ~spl7_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f105,f100,f95,f73,f108])).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    spl7_10 <=> ! [X1,X0] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | k1_funct_1(sK3,sK6(sK3,X1,X0)) = X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    sK2 = k1_funct_1(sK3,sK6(sK3,sK0,sK2)) | (~spl7_5 | ~spl7_9 | ~spl7_10)),
% 0.20/0.47    inference(resolution,[],[f104,f74])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    r2_hidden(sK2,k2_relat_1(sK3)) | ~spl7_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f73])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | k1_funct_1(sK3,sK6(sK3,sK0,X0)) = X0) ) | (~spl7_9 | ~spl7_10)),
% 0.20/0.47    inference(superposition,[],[f101,f96])).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | k1_funct_1(sK3,sK6(sK3,X1,X0)) = X0) ) | ~spl7_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f100])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    ~spl7_7 | spl7_10 | ~spl7_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f98,f62,f100,f81])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | k1_funct_1(sK3,sK6(sK3,X1,X0)) = X0 | ~v1_relat_1(sK3)) ) | ~spl7_3),
% 0.20/0.47    inference(resolution,[],[f50,f63])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    v1_funct_1(sK3) | ~spl7_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f62])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X6,X0,X1] : (~v1_funct_1(X0) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | k1_funct_1(X0,sK6(X0,X1,X6)) = X6 | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(equality_resolution,[],[f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK6(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    ~spl7_7 | spl7_9 | ~spl7_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f93,f78,f95,f81])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    spl7_6 <=> sK3 = k7_relat_1(sK3,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    k2_relat_1(sK3) = k9_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | ~spl7_6),
% 0.20/0.47    inference(superposition,[],[f44,f79])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    sK3 = k7_relat_1(sK3,sK0) | ~spl7_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f78])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    spl7_8),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f90])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    $false | spl7_8),
% 0.20/0.47    inference(resolution,[],[f88,f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl7_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f87])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    spl7_8 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    ~spl7_8 | ~spl7_2 | spl7_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f85,f81,f58,f87])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    spl7_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl7_2 | spl7_7)),
% 0.20/0.47    inference(resolution,[],[f84,f59])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f58])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl7_7),
% 0.20/0.47    inference(resolution,[],[f82,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    ~v1_relat_1(sK3) | spl7_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f81])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    spl7_6 | ~spl7_7 | ~spl7_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f76,f58,f81,f78])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    ~v1_relat_1(sK3) | sK3 = k7_relat_1(sK3,sK0) | ~spl7_2),
% 0.20/0.47    inference(resolution,[],[f65,f59])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_relat_1(X0) | k7_relat_1(X0,X1) = X0) )),
% 0.20/0.47    inference(resolution,[],[f45,f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.20/0.47    inference(pure_predicate_removal,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    spl7_5 | ~spl7_1 | ~spl7_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f71,f68,f54,f73])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    spl7_1 <=> r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    spl7_4 <=> k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    r2_hidden(sK2,k2_relat_1(sK3)) | (~spl7_1 | ~spl7_4)),
% 0.20/0.47    inference(superposition,[],[f55,f69])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | ~spl7_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f68])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) | ~spl7_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f54])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    spl7_4 | ~spl7_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f66,f58,f68])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | ~spl7_2),
% 0.20/0.47    inference(resolution,[],[f46,f59])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    spl7_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f30,f62])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    v1_funct_1(sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    spl7_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f31,f58])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    spl7_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f32,f54])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (31146)------------------------------
% 0.20/0.47  % (31146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (31146)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (31146)Memory used [KB]: 10746
% 0.20/0.47  % (31146)Time elapsed: 0.061 s
% 0.20/0.47  % (31146)------------------------------
% 0.20/0.47  % (31146)------------------------------
% 0.20/0.48  % (31137)Success in time 0.123 s
%------------------------------------------------------------------------------
