%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 144 expanded)
%              Number of leaves         :   21 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :  342 ( 610 expanded)
%              Number of equality atoms :   61 ( 119 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f239,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f65,f69,f75,f86,f173,f182,f210,f231,f238])).

fof(f238,plain,
    ( ~ spl7_5
    | ~ spl7_3
    | ~ spl7_4
    | spl7_10 ),
    inference(avatar_split_clause,[],[f232,f229,f73,f67,f78])).

fof(f78,plain,
    ( spl7_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f67,plain,
    ( spl7_3
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f73,plain,
    ( spl7_4
  <=> r2_hidden(sK0,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f229,plain,
    ( spl7_10
  <=> r2_hidden(sK6(sK3,sK0),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f232,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl7_10 ),
    inference(resolution,[],[f230,f56])).

fof(f56,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f24,f27,f26,f25])).

fof(f25,plain,(
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

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK4(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f230,plain,
    ( ~ r2_hidden(sK6(sK3,sK0),k1_relat_1(sK3))
    | spl7_10 ),
    inference(avatar_component_clause,[],[f229])).

fof(f231,plain,
    ( ~ spl7_10
    | ~ spl7_2
    | spl7_8
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f224,f208,f179,f63,f229])).

fof(f63,plain,
    ( spl7_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f179,plain,
    ( spl7_8
  <=> r2_hidden(sK6(sK3,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f208,plain,
    ( spl7_9
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f224,plain,
    ( ~ r2_hidden(sK6(sK3,sK0),k1_relat_1(sK3))
    | ~ spl7_2
    | spl7_8
    | ~ spl7_9 ),
    inference(resolution,[],[f223,f209])).

fof(f209,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
        | ~ r2_hidden(X0,k1_relat_1(sK3)) )
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f208])).

fof(f223,plain,
    ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(sK3,sK0),X3),sK3)
    | ~ spl7_2
    | spl7_8 ),
    inference(resolution,[],[f193,f64])).

fof(f64,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f193,plain,
    ( ! [X12,X10,X11] :
        ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(sK1,X12)))
        | ~ r2_hidden(k4_tarski(sK6(sK3,sK0),X10),X11) )
    | spl7_8 ),
    inference(resolution,[],[f184,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f184,plain,
    ( ! [X2,X3] : ~ r2_hidden(k4_tarski(sK6(sK3,sK0),X2),k2_zfmisc_1(sK1,X3))
    | spl7_8 ),
    inference(resolution,[],[f180,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f180,plain,
    ( ~ r2_hidden(sK6(sK3,sK0),sK1)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f179])).

fof(f210,plain,
    ( ~ spl7_5
    | spl7_9
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f206,f67,f208,f78])).

fof(f206,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl7_3 ),
    inference(resolution,[],[f57,f68])).

fof(f68,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f57,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f182,plain,
    ( ~ spl7_8
    | ~ spl7_4
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f177,f171,f73,f179])).

fof(f171,plain,
    ( spl7_7
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | k1_funct_1(sK3,sK6(sK3,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f177,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK3))
    | ~ r2_hidden(sK6(sK3,sK0),sK1)
    | ~ spl7_7 ),
    inference(equality_resolution,[],[f176])).

fof(f176,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(X0,k2_relat_1(sK3))
        | ~ r2_hidden(sK6(sK3,X0),sK1) )
    | ~ spl7_7 ),
    inference(resolution,[],[f174,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f174,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6(sK3,X0),sK1)
        | sK0 != X0
        | ~ r2_hidden(X0,k2_relat_1(sK3)) )
    | ~ spl7_7 ),
    inference(superposition,[],[f36,f172])).

fof(f172,plain,
    ( ! [X0] :
        ( k1_funct_1(sK3,sK6(sK3,X0)) = X0
        | ~ r2_hidden(X0,k2_relat_1(sK3)) )
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f171])).

fof(f36,plain,(
    ! [X4] :
      ( sK0 != k1_funct_1(sK3,X4)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ! [X4] :
        ( sK0 != k1_funct_1(sK3,X4)
        | ~ m1_subset_1(X4,sK1) )
    & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X0
            | ~ m1_subset_1(X4,X1) )
        & r2_hidden(X0,k2_relset_1(X1,X2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( sK0 != k1_funct_1(sK3,X4)
          | ~ m1_subset_1(X4,sK1) )
      & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

fof(f173,plain,
    ( ~ spl7_5
    | spl7_7
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f169,f67,f171,f78])).

fof(f169,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | k1_funct_1(sK3,sK6(sK3,X0)) = X0
        | ~ v1_relat_1(sK3) )
    | ~ spl7_3 ),
    inference(resolution,[],[f55,f68])).

fof(f55,plain,(
    ! [X0,X5] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,
    ( ~ spl7_2
    | spl7_5 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | ~ spl7_2
    | spl7_5 ),
    inference(subsumption_resolution,[],[f64,f84])).

fof(f84,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl7_5 ),
    inference(resolution,[],[f79,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f79,plain,
    ( ~ v1_relat_1(sK3)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f75,plain,
    ( ~ spl7_2
    | spl7_4
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f70,f59,f73,f63])).

fof(f59,plain,
    ( spl7_1
  <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f70,plain,
    ( r2_hidden(sK0,k2_relat_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_1 ),
    inference(superposition,[],[f60,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f60,plain,
    ( r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f69,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f33,f67])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f34,f63])).

fof(f34,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f35,f59])).

fof(f35,plain,(
    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n020.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:40:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (14020)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (14026)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (14027)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (14018)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (14019)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (14019)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (14016)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f239,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f61,f65,f69,f75,f86,f173,f182,f210,f231,f238])).
% 0.22/0.51  fof(f238,plain,(
% 0.22/0.51    ~spl7_5 | ~spl7_3 | ~spl7_4 | spl7_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f232,f229,f73,f67,f78])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    spl7_5 <=> v1_relat_1(sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    spl7_3 <=> v1_funct_1(sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    spl7_4 <=> r2_hidden(sK0,k2_relat_1(sK3))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.51  fof(f229,plain,(
% 0.22/0.51    spl7_10 <=> r2_hidden(sK6(sK3,sK0),k1_relat_1(sK3))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.51  fof(f232,plain,(
% 0.22/0.51    ~r2_hidden(sK0,k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl7_10),
% 0.22/0.51    inference(resolution,[],[f230,f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X0,X5] : (r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X0,X5,X1] : (r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & ((sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f24,f27,f26,f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(rectify,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.22/0.51  fof(f230,plain,(
% 0.22/0.51    ~r2_hidden(sK6(sK3,sK0),k1_relat_1(sK3)) | spl7_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f229])).
% 0.22/0.51  fof(f231,plain,(
% 0.22/0.51    ~spl7_10 | ~spl7_2 | spl7_8 | ~spl7_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f224,f208,f179,f63,f229])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    spl7_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.51  fof(f179,plain,(
% 0.22/0.51    spl7_8 <=> r2_hidden(sK6(sK3,sK0),sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.51  fof(f208,plain,(
% 0.22/0.51    spl7_9 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.51  fof(f224,plain,(
% 0.22/0.51    ~r2_hidden(sK6(sK3,sK0),k1_relat_1(sK3)) | (~spl7_2 | spl7_8 | ~spl7_9)),
% 0.22/0.51    inference(resolution,[],[f223,f209])).
% 0.22/0.51  fof(f209,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) | ~r2_hidden(X0,k1_relat_1(sK3))) ) | ~spl7_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f208])).
% 0.22/0.51  fof(f223,plain,(
% 0.22/0.51    ( ! [X3] : (~r2_hidden(k4_tarski(sK6(sK3,sK0),X3),sK3)) ) | (~spl7_2 | spl7_8)),
% 0.22/0.51    inference(resolution,[],[f193,f64])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl7_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f63])).
% 0.22/0.51  fof(f193,plain,(
% 0.22/0.51    ( ! [X12,X10,X11] : (~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(sK1,X12))) | ~r2_hidden(k4_tarski(sK6(sK3,sK0),X10),X11)) ) | spl7_8),
% 0.22/0.51    inference(resolution,[],[f184,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.51  fof(f184,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~r2_hidden(k4_tarski(sK6(sK3,sK0),X2),k2_zfmisc_1(sK1,X3))) ) | spl7_8),
% 0.22/0.51    inference(resolution,[],[f180,f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.51    inference(flattening,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.51    inference(nnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.51  fof(f180,plain,(
% 0.22/0.51    ~r2_hidden(sK6(sK3,sK0),sK1) | spl7_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f179])).
% 0.22/0.51  fof(f210,plain,(
% 0.22/0.51    ~spl7_5 | spl7_9 | ~spl7_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f206,f67,f208,f78])).
% 0.22/0.51  fof(f206,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) | ~v1_relat_1(sK3)) ) | ~spl7_3),
% 0.22/0.51    inference(resolution,[],[f57,f68])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    v1_funct_1(sK3) | ~spl7_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f67])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X2,X0] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~v1_relat_1(X2)) )),
% 0.22/0.51    inference(equality_resolution,[],[f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.51    inference(flattening,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.51    inference(nnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.51    inference(flattening,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.22/0.51  fof(f182,plain,(
% 0.22/0.51    ~spl7_8 | ~spl7_4 | ~spl7_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f177,f171,f73,f179])).
% 0.22/0.51  fof(f171,plain,(
% 0.22/0.51    spl7_7 <=> ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | k1_funct_1(sK3,sK6(sK3,X0)) = X0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.51  fof(f177,plain,(
% 0.22/0.51    ~r2_hidden(sK0,k2_relat_1(sK3)) | ~r2_hidden(sK6(sK3,sK0),sK1) | ~spl7_7),
% 0.22/0.51    inference(equality_resolution,[],[f176])).
% 0.22/0.51  fof(f176,plain,(
% 0.22/0.51    ( ! [X0] : (sK0 != X0 | ~r2_hidden(X0,k2_relat_1(sK3)) | ~r2_hidden(sK6(sK3,X0),sK1)) ) | ~spl7_7),
% 0.22/0.51    inference(resolution,[],[f174,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.51  fof(f174,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(sK6(sK3,X0),sK1) | sK0 != X0 | ~r2_hidden(X0,k2_relat_1(sK3))) ) | ~spl7_7),
% 0.22/0.51    inference(superposition,[],[f36,f172])).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    ( ! [X0] : (k1_funct_1(sK3,sK6(sK3,X0)) = X0 | ~r2_hidden(X0,k2_relat_1(sK3))) ) | ~spl7_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f171])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)) => (! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3))),
% 0.22/0.51    inference(flattening,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.22/0.51    inference(pure_predicate_removal,[],[f9])).
% 0.22/0.51  fof(f9,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.22/0.51    inference(negated_conjecture,[],[f8])).
% 0.22/0.51  fof(f8,conjecture,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).
% 0.22/0.51  fof(f173,plain,(
% 0.22/0.51    ~spl7_5 | spl7_7 | ~spl7_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f169,f67,f171,f78])).
% 0.22/0.51  fof(f169,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | k1_funct_1(sK3,sK6(sK3,X0)) = X0 | ~v1_relat_1(sK3)) ) | ~spl7_3),
% 0.22/0.51    inference(resolution,[],[f55,f68])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X0,X5] : (~v1_funct_1(X0) | ~r2_hidden(X5,k2_relat_1(X0)) | k1_funct_1(X0,sK6(X0,X5)) = X5 | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK6(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    ~spl7_2 | spl7_5),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f85])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    $false | (~spl7_2 | spl7_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f64,f84])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl7_5),
% 0.22/0.51    inference(resolution,[],[f79,f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    ~v1_relat_1(sK3) | spl7_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f78])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ~spl7_2 | spl7_4 | ~spl7_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f70,f59,f73,f63])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    spl7_1 <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    r2_hidden(sK0,k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl7_1),
% 0.22/0.51    inference(superposition,[],[f60,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) | ~spl7_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f59])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    spl7_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f33,f67])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    v1_funct_1(sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    spl7_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f34,f63])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    spl7_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f35,f59])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (14019)------------------------------
% 0.22/0.51  % (14019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (14019)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (14019)Memory used [KB]: 10874
% 0.22/0.51  % (14019)Time elapsed: 0.076 s
% 0.22/0.51  % (14019)------------------------------
% 0.22/0.51  % (14019)------------------------------
% 0.22/0.51  % (14028)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.52  % (14012)Success in time 0.149 s
%------------------------------------------------------------------------------
