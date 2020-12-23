%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 738 expanded)
%              Number of leaves         :   27 ( 254 expanded)
%              Depth                    :   16
%              Number of atoms          :  623 (3886 expanded)
%              Number of equality atoms :  184 (1218 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f638,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f99,f130,f165,f220,f309,f348,f363,f383,f614,f624,f634,f635])).

fof(f635,plain,
    ( ~ spl7_13
    | spl7_18
    | ~ spl7_1
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f628,f360,f87,f306,f275])).

fof(f275,plain,
    ( spl7_13
  <=> r2_hidden(sK5(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f306,plain,
    ( spl7_18
  <=> r2_hidden(sK4(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f87,plain,
    ( spl7_1
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK2,X0),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f360,plain,
    ( spl7_21
  <=> sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f628,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | ~ r2_hidden(sK5(sK2,sK1),sK0)
    | ~ spl7_1
    | ~ spl7_21 ),
    inference(superposition,[],[f88,f362])).

fof(f362,plain,
    ( sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1))
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f360])).

fof(f88,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,X0),sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f634,plain,
    ( spl7_20
    | ~ spl7_13
    | ~ spl7_3
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f633,f360,f96,f275,f322])).

fof(f322,plain,
    ( spl7_20
  <=> ! [X0] :
        ( sK4(sK2,X0) != sK4(sK2,sK1)
        | ~ r2_hidden(sK4(sK2,X0),X0)
        | k2_relat_1(sK2) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f96,plain,
    ( spl7_3
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f633,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK2,sK1),sK0)
        | sK4(sK2,X0) != sK4(sK2,sK1)
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK4(sK2,X0),X0) )
    | ~ spl7_3
    | ~ spl7_21 ),
    inference(forward_demodulation,[],[f632,f252])).

fof(f252,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f81,f98])).

fof(f98,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f81,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f40,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    & ! [X3] :
        ( ( k1_funct_1(sK2,sK3(X3)) = X3
          & r2_hidden(sK3(X3),sK0) )
        | ~ r2_hidden(X3,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f26,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != X1
        & ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) = X3
                & r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( sK1 != k2_relset_1(sK0,sK1,sK2)
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK2,X4) = X3
              & r2_hidden(X4,sK0) )
          | ~ r2_hidden(X3,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X3] :
      ( ? [X4] :
          ( k1_funct_1(sK2,X4) = X3
          & r2_hidden(X4,sK0) )
     => ( k1_funct_1(sK2,sK3(X3)) = X3
        & r2_hidden(sK3(X3),sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

fof(f632,plain,
    ( ! [X0] :
        ( sK4(sK2,X0) != sK4(sK2,sK1)
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2))
        | ~ r2_hidden(sK4(sK2,X0),X0) )
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f631,f82])).

fof(f82,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f40,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f631,plain,
    ( ! [X0] :
        ( sK4(sK2,X0) != sK4(sK2,sK1)
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2))
        | ~ r2_hidden(sK4(sK2,X0),X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f630,f38])).

fof(f38,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f630,plain,
    ( ! [X0] :
        ( sK4(sK2,X0) != sK4(sK2,sK1)
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2))
        | ~ r2_hidden(sK4(sK2,X0),X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_21 ),
    inference(superposition,[],[f50,f362])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X0,X3) != sK4(X0,X1)
      | k2_relat_1(X0) = X1
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(sK4(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f29,f32,f31,f30])).

fof(f30,plain,(
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

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK4(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f624,plain,
    ( spl7_12
    | spl7_13
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f623,f96,f275,f271])).

fof(f271,plain,
    ( spl7_12
  <=> sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f623,plain,
    ( r2_hidden(sK5(sK2,sK1),sK0)
    | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f539,f244])).

fof(f244,plain,(
    sK1 != k2_relat_1(sK2) ),
    inference(superposition,[],[f43,f80])).

fof(f80,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f40,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f43,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f539,plain,
    ( r2_hidden(sK5(sK2,sK1),sK0)
    | sK1 = k2_relat_1(sK2)
    | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))
    | ~ spl7_3 ),
    inference(resolution,[],[f258,f42])).

fof(f42,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | k1_funct_1(sK2,sK3(X3)) = X3 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f258,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(sK2,X1),sK0)
        | r2_hidden(sK4(sK2,X1),X1)
        | k2_relat_1(sK2) = X1 )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f257,f82])).

fof(f257,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(sK2,X1),sK0)
        | r2_hidden(sK4(sK2,X1),X1)
        | k2_relat_1(sK2) = X1
        | ~ v1_relat_1(sK2) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f254,f38])).

fof(f254,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(sK2,X1),sK0)
        | r2_hidden(sK4(sK2,X1),X1)
        | k2_relat_1(sK2) = X1
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_3 ),
    inference(superposition,[],[f48,f252])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK4(X0,X1),X1)
      | k2_relat_1(X0) = X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f614,plain,
    ( ~ spl7_18
    | ~ spl7_20 ),
    inference(avatar_contradiction_clause,[],[f613])).

fof(f613,plain,
    ( $false
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f612,f244])).

fof(f612,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f611,f308])).

fof(f308,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f306])).

fof(f611,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK1)
    | sK1 = k2_relat_1(sK2)
    | ~ spl7_20 ),
    inference(equality_resolution,[],[f323])).

fof(f323,plain,
    ( ! [X0] :
        ( sK4(sK2,X0) != sK4(sK2,sK1)
        | ~ r2_hidden(sK4(sK2,X0),X0)
        | k2_relat_1(sK2) = X0 )
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f322])).

fof(f383,plain,
    ( spl7_20
    | ~ spl7_17
    | ~ spl7_3
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f382,f271,f96,f302,f322])).

fof(f302,plain,
    ( spl7_17
  <=> r2_hidden(sK3(sK4(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f382,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK4(sK2,sK1)),sK0)
        | sK4(sK2,X0) != sK4(sK2,sK1)
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK4(sK2,X0),X0) )
    | ~ spl7_3
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f381,f252])).

fof(f381,plain,
    ( ! [X0] :
        ( sK4(sK2,X0) != sK4(sK2,sK1)
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2))
        | ~ r2_hidden(sK4(sK2,X0),X0) )
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f380,f82])).

fof(f380,plain,
    ( ! [X0] :
        ( sK4(sK2,X0) != sK4(sK2,sK1)
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2))
        | ~ r2_hidden(sK4(sK2,X0),X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f375,f38])).

fof(f375,plain,
    ( ! [X0] :
        ( sK4(sK2,X0) != sK4(sK2,sK1)
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2))
        | ~ r2_hidden(sK4(sK2,X0),X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_12 ),
    inference(superposition,[],[f50,f273])).

fof(f273,plain,
    ( sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f271])).

fof(f363,plain,
    ( spl7_12
    | spl7_21 ),
    inference(avatar_split_clause,[],[f358,f360,f271])).

fof(f358,plain,
    ( sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1))
    | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) ),
    inference(subsumption_resolution,[],[f357,f82])).

fof(f357,plain,
    ( sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1))
    | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f326,f244])).

fof(f326,plain,
    ( sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1))
    | sK1 = k2_relat_1(sK2)
    | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f249,f38])).

fof(f249,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | sK4(X1,sK1) = k1_funct_1(X1,sK5(X1,sK1))
      | sK1 = k2_relat_1(X1)
      | sK4(X1,sK1) = k1_funct_1(sK2,sK3(sK4(X1,sK1)))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f42,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
      | k2_relat_1(X0) = X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f348,plain,
    ( ~ spl7_1
    | ~ spl7_3
    | spl7_17 ),
    inference(avatar_contradiction_clause,[],[f347])).

fof(f347,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_3
    | spl7_17 ),
    inference(subsumption_resolution,[],[f346,f333])).

fof(f333,plain,
    ( r2_hidden(sK5(sK2,sK1),sK0)
    | ~ spl7_3
    | spl7_17 ),
    inference(forward_demodulation,[],[f332,f252])).

fof(f332,plain,
    ( r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2))
    | spl7_17 ),
    inference(subsumption_resolution,[],[f331,f82])).

fof(f331,plain,
    ( r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | spl7_17 ),
    inference(subsumption_resolution,[],[f330,f38])).

fof(f330,plain,
    ( r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_17 ),
    inference(subsumption_resolution,[],[f327,f244])).

fof(f327,plain,
    ( r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2))
    | sK1 = k2_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_17 ),
    inference(resolution,[],[f325,f48])).

fof(f325,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK1)
    | spl7_17 ),
    inference(resolution,[],[f304,f41])).

fof(f41,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f304,plain,
    ( ~ r2_hidden(sK3(sK4(sK2,sK1)),sK0)
    | spl7_17 ),
    inference(avatar_component_clause,[],[f302])).

fof(f346,plain,
    ( ~ r2_hidden(sK5(sK2,sK1),sK0)
    | ~ spl7_1
    | spl7_17 ),
    inference(subsumption_resolution,[],[f343,f325])).

fof(f343,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | ~ r2_hidden(sK5(sK2,sK1),sK0)
    | ~ spl7_1
    | spl7_17 ),
    inference(superposition,[],[f88,f336])).

fof(f336,plain,
    ( sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1))
    | spl7_17 ),
    inference(subsumption_resolution,[],[f335,f82])).

fof(f335,plain,
    ( sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | spl7_17 ),
    inference(subsumption_resolution,[],[f334,f38])).

fof(f334,plain,
    ( sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_17 ),
    inference(subsumption_resolution,[],[f328,f244])).

fof(f328,plain,
    ( sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1))
    | sK1 = k2_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_17 ),
    inference(resolution,[],[f325,f49])).

fof(f309,plain,
    ( ~ spl7_17
    | spl7_18
    | ~ spl7_1
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f298,f271,f87,f306,f302])).

fof(f298,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | ~ r2_hidden(sK3(sK4(sK2,sK1)),sK0)
    | ~ spl7_1
    | ~ spl7_12 ),
    inference(superposition,[],[f88,f273])).

fof(f220,plain,
    ( ~ spl7_2
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f218,f44])).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f218,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK2))
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f217,f212])).

fof(f212,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(superposition,[],[f184,f189])).

fof(f189,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(resolution,[],[f171,f58])).

fof(f171,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f100,f129])).

fof(f129,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl7_7
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f100,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f40,f92])).

fof(f92,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f184,plain,
    ( k1_xboole_0 != k2_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f113,f129])).

fof(f113,plain,
    ( k1_xboole_0 != k2_relset_1(sK0,k1_xboole_0,sK2)
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f43,f92])).

fof(f217,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(sK2))
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(resolution,[],[f215,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f215,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(resolution,[],[f214,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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

fof(f214,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f213,f171])).

fof(f213,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(superposition,[],[f59,f189])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f165,plain,
    ( ~ spl7_2
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f163,f44])).

fof(f163,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f162,f157])).

fof(f157,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(superposition,[],[f137,f142])).

fof(f142,plain,
    ( k2_relset_1(sK0,k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(resolution,[],[f131,f58])).

fof(f131,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f100,f125])).

fof(f125,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl7_6
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f137,plain,
    ( k1_xboole_0 != k2_relset_1(sK0,k1_xboole_0,k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f113,f125])).

fof(f162,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(resolution,[],[f161,f53])).

fof(f161,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(resolution,[],[f159,f54])).

fof(f159,plain,
    ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f158,f131])).

fof(f158,plain,
    ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(superposition,[],[f59,f142])).

fof(f130,plain,
    ( spl7_6
    | spl7_7
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f121,f90,f127,f123])).

fof(f121,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f114,f101])).

fof(f101,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f39,f92])).

fof(f39,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f114,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl7_2 ),
    inference(resolution,[],[f100,f75])).

fof(f75,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f99,plain,
    ( spl7_3
    | spl7_2 ),
    inference(avatar_split_clause,[],[f94,f90,f96])).

fof(f94,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f79,f39])).

fof(f79,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f40,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f93,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f85,f90,f87])).

fof(f85,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ r2_hidden(X0,sK0)
      | r2_hidden(k1_funct_1(sK2,X0),sK1) ) ),
    inference(subsumption_resolution,[],[f84,f38])).

fof(f84,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ r2_hidden(X0,sK0)
      | r2_hidden(k1_funct_1(sK2,X0),sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f78,f39])).

fof(f78,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ r2_hidden(X0,sK0)
      | r2_hidden(k1_funct_1(sK2,X0),sK1)
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f40,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | r2_hidden(k1_funct_1(X3,X2),X1)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:54:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (31831)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.48  % (31846)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.48  % (31847)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.50  % (31833)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (31838)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (31830)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (31840)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (31850)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (31828)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (31829)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (31842)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (31839)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (31845)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (31834)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (31836)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (31843)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (31844)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (31841)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (31852)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (31851)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (31848)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (31849)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (31832)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (31835)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.53  % (31837)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.54  % (31853)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.54  % (31829)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f638,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f93,f99,f130,f165,f220,f309,f348,f363,f383,f614,f624,f634,f635])).
% 0.21/0.54  fof(f635,plain,(
% 0.21/0.54    ~spl7_13 | spl7_18 | ~spl7_1 | ~spl7_21),
% 0.21/0.54    inference(avatar_split_clause,[],[f628,f360,f87,f306,f275])).
% 0.21/0.54  fof(f275,plain,(
% 0.21/0.54    spl7_13 <=> r2_hidden(sK5(sK2,sK1),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.54  fof(f306,plain,(
% 0.21/0.54    spl7_18 <=> r2_hidden(sK4(sK2,sK1),sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    spl7_1 <=> ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK2,X0),sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.54  fof(f360,plain,(
% 0.21/0.54    spl7_21 <=> sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.54  fof(f628,plain,(
% 0.21/0.54    r2_hidden(sK4(sK2,sK1),sK1) | ~r2_hidden(sK5(sK2,sK1),sK0) | (~spl7_1 | ~spl7_21)),
% 0.21/0.54    inference(superposition,[],[f88,f362])).
% 0.21/0.54  fof(f362,plain,(
% 0.21/0.54    sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1)) | ~spl7_21),
% 0.21/0.54    inference(avatar_component_clause,[],[f360])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),sK1) | ~r2_hidden(X0,sK0)) ) | ~spl7_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f87])).
% 0.21/0.54  fof(f634,plain,(
% 0.21/0.54    spl7_20 | ~spl7_13 | ~spl7_3 | ~spl7_21),
% 0.21/0.54    inference(avatar_split_clause,[],[f633,f360,f96,f275,f322])).
% 0.21/0.54  fof(f322,plain,(
% 0.21/0.54    spl7_20 <=> ! [X0] : (sK4(sK2,X0) != sK4(sK2,sK1) | ~r2_hidden(sK4(sK2,X0),X0) | k2_relat_1(sK2) = X0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    spl7_3 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.54  fof(f633,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(sK5(sK2,sK1),sK0) | sK4(sK2,X0) != sK4(sK2,sK1) | k2_relat_1(sK2) = X0 | ~r2_hidden(sK4(sK2,X0),X0)) ) | (~spl7_3 | ~spl7_21)),
% 0.21/0.54    inference(forward_demodulation,[],[f632,f252])).
% 0.21/0.54  fof(f252,plain,(
% 0.21/0.54    sK0 = k1_relat_1(sK2) | ~spl7_3),
% 0.21/0.54    inference(forward_demodulation,[],[f81,f98])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl7_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f96])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.21/0.54    inference(resolution,[],[f40,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    sK1 != k2_relset_1(sK0,sK1,sK2) & ! [X3] : ((k1_funct_1(sK2,sK3(X3)) = X3 & r2_hidden(sK3(X3),sK0)) | ~r2_hidden(X3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f26,f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (sK1 != k2_relset_1(sK0,sK1,sK2) & ! [X3] : (? [X4] : (k1_funct_1(sK2,X4) = X3 & r2_hidden(X4,sK0)) | ~r2_hidden(X3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X3] : (? [X4] : (k1_funct_1(sK2,X4) = X3 & r2_hidden(X4,sK0)) => (k1_funct_1(sK2,sK3(X3)) = X3 & r2_hidden(sK3(X3),sK0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.54    inference(flattening,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.54    inference(negated_conjecture,[],[f11])).
% 0.21/0.54  fof(f11,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).
% 0.21/0.54  fof(f632,plain,(
% 0.21/0.54    ( ! [X0] : (sK4(sK2,X0) != sK4(sK2,sK1) | k2_relat_1(sK2) = X0 | ~r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2)) | ~r2_hidden(sK4(sK2,X0),X0)) ) | ~spl7_21),
% 0.21/0.54    inference(subsumption_resolution,[],[f631,f82])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    v1_relat_1(sK2)),
% 0.21/0.54    inference(resolution,[],[f40,f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.54  fof(f631,plain,(
% 0.21/0.54    ( ! [X0] : (sK4(sK2,X0) != sK4(sK2,sK1) | k2_relat_1(sK2) = X0 | ~r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2)) | ~r2_hidden(sK4(sK2,X0),X0) | ~v1_relat_1(sK2)) ) | ~spl7_21),
% 0.21/0.54    inference(subsumption_resolution,[],[f630,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    v1_funct_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f630,plain,(
% 0.21/0.54    ( ! [X0] : (sK4(sK2,X0) != sK4(sK2,sK1) | k2_relat_1(sK2) = X0 | ~r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2)) | ~r2_hidden(sK4(sK2,X0),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl7_21),
% 0.21/0.54    inference(superposition,[],[f50,f362])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (k1_funct_1(X0,X3) != sK4(X0,X1) | k2_relat_1(X0) = X1 | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(sK4(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & ((sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f29,f32,f31,f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(rectify,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.21/0.54  fof(f624,plain,(
% 0.21/0.54    spl7_12 | spl7_13 | ~spl7_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f623,f96,f275,f271])).
% 0.21/0.54  fof(f271,plain,(
% 0.21/0.54    spl7_12 <=> sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.54  fof(f623,plain,(
% 0.21/0.54    r2_hidden(sK5(sK2,sK1),sK0) | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) | ~spl7_3),
% 0.21/0.54    inference(subsumption_resolution,[],[f539,f244])).
% 0.21/0.54  fof(f244,plain,(
% 0.21/0.54    sK1 != k2_relat_1(sK2)),
% 0.21/0.54    inference(superposition,[],[f43,f80])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.54    inference(resolution,[],[f40,f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f539,plain,(
% 0.21/0.54    r2_hidden(sK5(sK2,sK1),sK0) | sK1 = k2_relat_1(sK2) | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) | ~spl7_3),
% 0.21/0.54    inference(resolution,[],[f258,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X3] : (~r2_hidden(X3,sK1) | k1_funct_1(sK2,sK3(X3)) = X3) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f258,plain,(
% 0.21/0.54    ( ! [X1] : (r2_hidden(sK5(sK2,X1),sK0) | r2_hidden(sK4(sK2,X1),X1) | k2_relat_1(sK2) = X1) ) | ~spl7_3),
% 0.21/0.54    inference(subsumption_resolution,[],[f257,f82])).
% 0.21/0.54  fof(f257,plain,(
% 0.21/0.54    ( ! [X1] : (r2_hidden(sK5(sK2,X1),sK0) | r2_hidden(sK4(sK2,X1),X1) | k2_relat_1(sK2) = X1 | ~v1_relat_1(sK2)) ) | ~spl7_3),
% 0.21/0.54    inference(subsumption_resolution,[],[f254,f38])).
% 0.21/0.54  fof(f254,plain,(
% 0.21/0.54    ( ! [X1] : (r2_hidden(sK5(sK2,X1),sK0) | r2_hidden(sK4(sK2,X1),X1) | k2_relat_1(sK2) = X1 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl7_3),
% 0.21/0.54    inference(superposition,[],[f48,f252])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | r2_hidden(sK4(X0,X1),X1) | k2_relat_1(X0) = X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f614,plain,(
% 0.21/0.54    ~spl7_18 | ~spl7_20),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f613])).
% 0.21/0.54  fof(f613,plain,(
% 0.21/0.54    $false | (~spl7_18 | ~spl7_20)),
% 0.21/0.54    inference(subsumption_resolution,[],[f612,f244])).
% 0.21/0.54  fof(f612,plain,(
% 0.21/0.54    sK1 = k2_relat_1(sK2) | (~spl7_18 | ~spl7_20)),
% 0.21/0.54    inference(subsumption_resolution,[],[f611,f308])).
% 0.21/0.54  fof(f308,plain,(
% 0.21/0.54    r2_hidden(sK4(sK2,sK1),sK1) | ~spl7_18),
% 0.21/0.54    inference(avatar_component_clause,[],[f306])).
% 0.21/0.54  fof(f611,plain,(
% 0.21/0.54    ~r2_hidden(sK4(sK2,sK1),sK1) | sK1 = k2_relat_1(sK2) | ~spl7_20),
% 0.21/0.54    inference(equality_resolution,[],[f323])).
% 0.21/0.54  fof(f323,plain,(
% 0.21/0.54    ( ! [X0] : (sK4(sK2,X0) != sK4(sK2,sK1) | ~r2_hidden(sK4(sK2,X0),X0) | k2_relat_1(sK2) = X0) ) | ~spl7_20),
% 0.21/0.54    inference(avatar_component_clause,[],[f322])).
% 0.21/0.54  fof(f383,plain,(
% 0.21/0.54    spl7_20 | ~spl7_17 | ~spl7_3 | ~spl7_12),
% 0.21/0.54    inference(avatar_split_clause,[],[f382,f271,f96,f302,f322])).
% 0.21/0.54  fof(f302,plain,(
% 0.21/0.54    spl7_17 <=> r2_hidden(sK3(sK4(sK2,sK1)),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.21/0.54  fof(f382,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(sK3(sK4(sK2,sK1)),sK0) | sK4(sK2,X0) != sK4(sK2,sK1) | k2_relat_1(sK2) = X0 | ~r2_hidden(sK4(sK2,X0),X0)) ) | (~spl7_3 | ~spl7_12)),
% 0.21/0.54    inference(forward_demodulation,[],[f381,f252])).
% 0.21/0.54  fof(f381,plain,(
% 0.21/0.54    ( ! [X0] : (sK4(sK2,X0) != sK4(sK2,sK1) | k2_relat_1(sK2) = X0 | ~r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2)) | ~r2_hidden(sK4(sK2,X0),X0)) ) | ~spl7_12),
% 0.21/0.54    inference(subsumption_resolution,[],[f380,f82])).
% 0.21/0.54  fof(f380,plain,(
% 0.21/0.54    ( ! [X0] : (sK4(sK2,X0) != sK4(sK2,sK1) | k2_relat_1(sK2) = X0 | ~r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2)) | ~r2_hidden(sK4(sK2,X0),X0) | ~v1_relat_1(sK2)) ) | ~spl7_12),
% 0.21/0.54    inference(subsumption_resolution,[],[f375,f38])).
% 0.21/0.54  fof(f375,plain,(
% 0.21/0.54    ( ! [X0] : (sK4(sK2,X0) != sK4(sK2,sK1) | k2_relat_1(sK2) = X0 | ~r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2)) | ~r2_hidden(sK4(sK2,X0),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl7_12),
% 0.21/0.54    inference(superposition,[],[f50,f273])).
% 0.21/0.54  fof(f273,plain,(
% 0.21/0.54    sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) | ~spl7_12),
% 0.21/0.54    inference(avatar_component_clause,[],[f271])).
% 0.21/0.54  fof(f363,plain,(
% 0.21/0.54    spl7_12 | spl7_21),
% 0.21/0.54    inference(avatar_split_clause,[],[f358,f360,f271])).
% 0.21/0.54  fof(f358,plain,(
% 0.21/0.54    sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1)) | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))),
% 0.21/0.54    inference(subsumption_resolution,[],[f357,f82])).
% 0.21/0.54  fof(f357,plain,(
% 0.21/0.54    sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1)) | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) | ~v1_relat_1(sK2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f326,f244])).
% 0.21/0.54  fof(f326,plain,(
% 0.21/0.54    sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1)) | sK1 = k2_relat_1(sK2) | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) | ~v1_relat_1(sK2)),
% 0.21/0.54    inference(resolution,[],[f249,f38])).
% 0.21/0.54  fof(f249,plain,(
% 0.21/0.54    ( ! [X1] : (~v1_funct_1(X1) | sK4(X1,sK1) = k1_funct_1(X1,sK5(X1,sK1)) | sK1 = k2_relat_1(X1) | sK4(X1,sK1) = k1_funct_1(sK2,sK3(sK4(X1,sK1))) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(resolution,[],[f42,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) | k2_relat_1(X0) = X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f348,plain,(
% 0.21/0.54    ~spl7_1 | ~spl7_3 | spl7_17),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f347])).
% 0.21/0.54  fof(f347,plain,(
% 0.21/0.54    $false | (~spl7_1 | ~spl7_3 | spl7_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f346,f333])).
% 0.21/0.54  fof(f333,plain,(
% 0.21/0.54    r2_hidden(sK5(sK2,sK1),sK0) | (~spl7_3 | spl7_17)),
% 0.21/0.54    inference(forward_demodulation,[],[f332,f252])).
% 0.21/0.54  fof(f332,plain,(
% 0.21/0.54    r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2)) | spl7_17),
% 0.21/0.54    inference(subsumption_resolution,[],[f331,f82])).
% 0.21/0.54  fof(f331,plain,(
% 0.21/0.54    r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | spl7_17),
% 0.21/0.54    inference(subsumption_resolution,[],[f330,f38])).
% 0.21/0.54  fof(f330,plain,(
% 0.21/0.54    r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl7_17),
% 0.21/0.54    inference(subsumption_resolution,[],[f327,f244])).
% 0.21/0.54  fof(f327,plain,(
% 0.21/0.54    r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2)) | sK1 = k2_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl7_17),
% 0.21/0.54    inference(resolution,[],[f325,f48])).
% 0.21/0.54  fof(f325,plain,(
% 0.21/0.54    ~r2_hidden(sK4(sK2,sK1),sK1) | spl7_17),
% 0.21/0.54    inference(resolution,[],[f304,f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f304,plain,(
% 0.21/0.55    ~r2_hidden(sK3(sK4(sK2,sK1)),sK0) | spl7_17),
% 0.21/0.55    inference(avatar_component_clause,[],[f302])).
% 0.21/0.55  fof(f346,plain,(
% 0.21/0.55    ~r2_hidden(sK5(sK2,sK1),sK0) | (~spl7_1 | spl7_17)),
% 0.21/0.55    inference(subsumption_resolution,[],[f343,f325])).
% 0.21/0.55  fof(f343,plain,(
% 0.21/0.55    r2_hidden(sK4(sK2,sK1),sK1) | ~r2_hidden(sK5(sK2,sK1),sK0) | (~spl7_1 | spl7_17)),
% 0.21/0.55    inference(superposition,[],[f88,f336])).
% 0.21/0.55  fof(f336,plain,(
% 0.21/0.55    sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1)) | spl7_17),
% 0.21/0.55    inference(subsumption_resolution,[],[f335,f82])).
% 0.21/0.55  fof(f335,plain,(
% 0.21/0.55    sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1)) | ~v1_relat_1(sK2) | spl7_17),
% 0.21/0.55    inference(subsumption_resolution,[],[f334,f38])).
% 0.21/0.55  fof(f334,plain,(
% 0.21/0.55    sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl7_17),
% 0.21/0.55    inference(subsumption_resolution,[],[f328,f244])).
% 0.21/0.55  fof(f328,plain,(
% 0.21/0.55    sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1)) | sK1 = k2_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl7_17),
% 0.21/0.55    inference(resolution,[],[f325,f49])).
% 0.21/0.55  fof(f309,plain,(
% 0.21/0.55    ~spl7_17 | spl7_18 | ~spl7_1 | ~spl7_12),
% 0.21/0.55    inference(avatar_split_clause,[],[f298,f271,f87,f306,f302])).
% 0.21/0.55  fof(f298,plain,(
% 0.21/0.55    r2_hidden(sK4(sK2,sK1),sK1) | ~r2_hidden(sK3(sK4(sK2,sK1)),sK0) | (~spl7_1 | ~spl7_12)),
% 0.21/0.55    inference(superposition,[],[f88,f273])).
% 0.21/0.55  fof(f220,plain,(
% 0.21/0.55    ~spl7_2 | ~spl7_7),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f219])).
% 0.21/0.55  fof(f219,plain,(
% 0.21/0.55    $false | (~spl7_2 | ~spl7_7)),
% 0.21/0.55    inference(subsumption_resolution,[],[f218,f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.55  fof(f218,plain,(
% 0.21/0.55    ~r1_tarski(k1_xboole_0,k2_relat_1(sK2)) | (~spl7_2 | ~spl7_7)),
% 0.21/0.55    inference(subsumption_resolution,[],[f217,f212])).
% 0.21/0.55  fof(f212,plain,(
% 0.21/0.55    k1_xboole_0 != k2_relat_1(sK2) | (~spl7_2 | ~spl7_7)),
% 0.21/0.55    inference(superposition,[],[f184,f189])).
% 0.21/0.55  fof(f189,plain,(
% 0.21/0.55    k2_relat_1(sK2) = k2_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl7_2 | ~spl7_7)),
% 0.21/0.55    inference(resolution,[],[f171,f58])).
% 0.21/0.55  fof(f171,plain,(
% 0.21/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl7_2 | ~spl7_7)),
% 0.21/0.55    inference(forward_demodulation,[],[f100,f129])).
% 0.21/0.55  fof(f129,plain,(
% 0.21/0.55    k1_xboole_0 = sK0 | ~spl7_7),
% 0.21/0.55    inference(avatar_component_clause,[],[f127])).
% 0.21/0.55  fof(f127,plain,(
% 0.21/0.55    spl7_7 <=> k1_xboole_0 = sK0),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.55  fof(f100,plain,(
% 0.21/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl7_2),
% 0.21/0.55    inference(backward_demodulation,[],[f40,f92])).
% 0.21/0.55  fof(f92,plain,(
% 0.21/0.55    k1_xboole_0 = sK1 | ~spl7_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f90])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    spl7_2 <=> k1_xboole_0 = sK1),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.55  fof(f184,plain,(
% 0.21/0.55    k1_xboole_0 != k2_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl7_2 | ~spl7_7)),
% 0.21/0.55    inference(forward_demodulation,[],[f113,f129])).
% 0.21/0.55  fof(f113,plain,(
% 0.21/0.55    k1_xboole_0 != k2_relset_1(sK0,k1_xboole_0,sK2) | ~spl7_2),
% 0.21/0.55    inference(forward_demodulation,[],[f43,f92])).
% 0.21/0.55  fof(f217,plain,(
% 0.21/0.55    k1_xboole_0 = k2_relat_1(sK2) | ~r1_tarski(k1_xboole_0,k2_relat_1(sK2)) | (~spl7_2 | ~spl7_7)),
% 0.21/0.55    inference(resolution,[],[f215,f53])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.55    inference(flattening,[],[f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.55  fof(f215,plain,(
% 0.21/0.55    r1_tarski(k2_relat_1(sK2),k1_xboole_0) | (~spl7_2 | ~spl7_7)),
% 0.21/0.55    inference(resolution,[],[f214,f54])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.55    inference(nnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.55  fof(f214,plain,(
% 0.21/0.55    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (~spl7_2 | ~spl7_7)),
% 0.21/0.55    inference(subsumption_resolution,[],[f213,f171])).
% 0.21/0.55  fof(f213,plain,(
% 0.21/0.55    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl7_2 | ~spl7_7)),
% 0.21/0.55    inference(superposition,[],[f59,f189])).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.55  fof(f165,plain,(
% 0.21/0.55    ~spl7_2 | ~spl7_6),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f164])).
% 0.21/0.55  fof(f164,plain,(
% 0.21/0.55    $false | (~spl7_2 | ~spl7_6)),
% 0.21/0.55    inference(subsumption_resolution,[],[f163,f44])).
% 0.21/0.55  fof(f163,plain,(
% 0.21/0.55    ~r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0)) | (~spl7_2 | ~spl7_6)),
% 0.21/0.55    inference(subsumption_resolution,[],[f162,f157])).
% 0.21/0.55  fof(f157,plain,(
% 0.21/0.55    k1_xboole_0 != k2_relat_1(k1_xboole_0) | (~spl7_2 | ~spl7_6)),
% 0.21/0.55    inference(superposition,[],[f137,f142])).
% 0.21/0.55  fof(f142,plain,(
% 0.21/0.55    k2_relset_1(sK0,k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0) | (~spl7_2 | ~spl7_6)),
% 0.21/0.55    inference(resolution,[],[f131,f58])).
% 0.21/0.55  fof(f131,plain,(
% 0.21/0.55    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl7_2 | ~spl7_6)),
% 0.21/0.55    inference(backward_demodulation,[],[f100,f125])).
% 0.21/0.55  fof(f125,plain,(
% 0.21/0.55    k1_xboole_0 = sK2 | ~spl7_6),
% 0.21/0.55    inference(avatar_component_clause,[],[f123])).
% 0.21/0.55  fof(f123,plain,(
% 0.21/0.55    spl7_6 <=> k1_xboole_0 = sK2),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.55  fof(f137,plain,(
% 0.21/0.55    k1_xboole_0 != k2_relset_1(sK0,k1_xboole_0,k1_xboole_0) | (~spl7_2 | ~spl7_6)),
% 0.21/0.55    inference(forward_demodulation,[],[f113,f125])).
% 0.21/0.55  fof(f162,plain,(
% 0.21/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0)) | (~spl7_2 | ~spl7_6)),
% 0.21/0.55    inference(resolution,[],[f161,f53])).
% 0.21/0.55  fof(f161,plain,(
% 0.21/0.55    r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) | (~spl7_2 | ~spl7_6)),
% 0.21/0.55    inference(resolution,[],[f159,f54])).
% 0.21/0.55  fof(f159,plain,(
% 0.21/0.55    m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl7_2 | ~spl7_6)),
% 0.21/0.55    inference(subsumption_resolution,[],[f158,f131])).
% 0.21/0.55  fof(f158,plain,(
% 0.21/0.55    m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl7_2 | ~spl7_6)),
% 0.21/0.55    inference(superposition,[],[f59,f142])).
% 0.21/0.55  fof(f130,plain,(
% 0.21/0.55    spl7_6 | spl7_7 | ~spl7_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f121,f90,f127,f123])).
% 0.21/0.55  fof(f121,plain,(
% 0.21/0.55    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl7_2),
% 0.21/0.55    inference(subsumption_resolution,[],[f114,f101])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl7_2),
% 0.21/0.55    inference(backward_demodulation,[],[f39,f92])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f114,plain,(
% 0.21/0.55    ~v1_funct_2(sK2,sK0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl7_2),
% 0.21/0.55    inference(resolution,[],[f100,f75])).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 0.21/0.55    inference(equality_resolution,[],[f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(nnf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(flattening,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(ennf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    spl7_3 | spl7_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f94,f90,f96])).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.55    inference(subsumption_resolution,[],[f79,f39])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.55    inference(resolution,[],[f40,f60])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f37])).
% 0.21/0.55  fof(f93,plain,(
% 0.21/0.55    spl7_1 | spl7_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f85,f90,f87])).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = sK1 | ~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK2,X0),sK1)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f84,f38])).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = sK1 | ~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK2,X0),sK1) | ~v1_funct_1(sK2)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f78,f39])).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = sK1 | ~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK2,X0),sK1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 0.21/0.55    inference(resolution,[],[f40,f66])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | r2_hidden(k1_funct_1(X3,X2),X1) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.55    inference(flattening,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (31829)------------------------------
% 0.21/0.56  % (31829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (31829)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (31829)Memory used [KB]: 10874
% 0.21/0.56  % (31829)Time elapsed: 0.124 s
% 0.21/0.56  % (31829)------------------------------
% 0.21/0.56  % (31829)------------------------------
% 0.21/0.56  % (31827)Success in time 0.199 s
%------------------------------------------------------------------------------
