%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 209 expanded)
%              Number of leaves         :   32 (  95 expanded)
%              Depth                    :   11
%              Number of atoms          :  491 (1063 expanded)
%              Number of equality atoms :  112 ( 243 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f197,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f88,f92,f96,f100,f104,f108,f112,f126,f129,f135,f155,f168,f175,f188,f192,f196])).

fof(f196,plain,
    ( ~ spl11_3
    | spl11_12
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f194,f190,f133,f90])).

fof(f90,plain,
    ( spl11_3
  <=> r2_hidden(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f133,plain,
    ( spl11_12
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f190,plain,
    ( spl11_20
  <=> ! [X0] :
        ( r2_hidden(sK4,k9_relat_1(sK3,X0))
        | ~ r2_hidden(sK5,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f194,plain,
    ( ~ r2_hidden(sK5,sK2)
    | spl11_12
    | ~ spl11_20 ),
    inference(resolution,[],[f191,f134])).

fof(f134,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | spl11_12 ),
    inference(avatar_component_clause,[],[f133])).

fof(f191,plain,
    ( ! [X0] :
        ( r2_hidden(sK4,k9_relat_1(sK3,X0))
        | ~ r2_hidden(sK5,X0) )
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f190])).

fof(f192,plain,
    ( ~ spl11_14
    | spl11_20
    | ~ spl11_2
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f176,f166,f86,f190,f144])).

fof(f144,plain,
    ( spl11_14
  <=> r2_hidden(sK5,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f86,plain,
    ( spl11_2
  <=> sK4 = k1_funct_1(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f166,plain,
    ( spl11_18
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | r2_hidden(k1_funct_1(sK3,X0),k9_relat_1(sK3,X1))
        | ~ r2_hidden(X0,k1_relat_1(sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f176,plain,
    ( ! [X0] :
        ( r2_hidden(sK4,k9_relat_1(sK3,X0))
        | ~ r2_hidden(sK5,X0)
        | ~ r2_hidden(sK5,k1_relat_1(sK3)) )
    | ~ spl11_2
    | ~ spl11_18 ),
    inference(superposition,[],[f167,f87])).

fof(f87,plain,
    ( sK4 = k1_funct_1(sK3,sK5)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f167,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k1_funct_1(sK3,X0),k9_relat_1(sK3,X1))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_relat_1(sK3)) )
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f166])).

fof(f188,plain,
    ( ~ spl11_4
    | ~ spl11_6
    | ~ spl11_16
    | ~ spl11_19 ),
    inference(avatar_split_clause,[],[f186,f171,f153,f102,f94])).

fof(f94,plain,
    ( spl11_4
  <=> r2_hidden(sK5,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f102,plain,
    ( spl11_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f153,plain,
    ( spl11_16
  <=> ! [X0] : ~ r2_hidden(k4_tarski(sK5,X0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f171,plain,
    ( spl11_19
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f186,plain,
    ( ~ r2_hidden(sK5,sK0)
    | ~ spl11_6
    | ~ spl11_16
    | ~ spl11_19 ),
    inference(resolution,[],[f184,f154])).

fof(f154,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK5,X0),sK3)
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f153])).

fof(f184,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK9(sK3,X0)),sK3)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl11_6
    | ~ spl11_19 ),
    inference(trivial_inequality_removal,[],[f183])).

fof(f183,plain,
    ( ! [X0] :
        ( sK0 != sK0
        | ~ r2_hidden(X0,sK0)
        | r2_hidden(k4_tarski(X0,sK9(sK3,X0)),sK3) )
    | ~ spl11_6
    | ~ spl11_19 ),
    inference(forward_demodulation,[],[f182,f172])).

fof(f172,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f171])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | sK0 != k1_relset_1(sK0,sK1,sK3)
        | r2_hidden(k4_tarski(X0,sK9(sK3,X0)),sK3) )
    | ~ spl11_6 ),
    inference(resolution,[],[f65,f103])).

fof(f103,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_hidden(X3,X1)
      | k1_relset_1(X1,X0,X2) != X1
      | r2_hidden(k4_tarski(X3,sK9(X2,X3)),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK9(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK10(X1,X2),X6),X2)
            & r2_hidden(sK10(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f33,f35,f34])).

fof(f34,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK9(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK10(X1,X2),X6),X2)
        & r2_hidden(sK10(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X5] :
              ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
              & r2_hidden(X5,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

fof(f175,plain,
    ( spl11_19
    | spl11_5
    | ~ spl11_7
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f169,f102,f106,f98,f171])).

fof(f98,plain,
    ( spl11_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f106,plain,
    ( spl11_7
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f169,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl11_6 ),
    inference(resolution,[],[f57,f103])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f168,plain,
    ( ~ spl11_9
    | spl11_18
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f164,f110,f166,f115])).

fof(f115,plain,
    ( spl11_9
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f110,plain,
    ( spl11_8
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f164,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_relat_1(sK3))
        | r2_hidden(k1_funct_1(sK3,X0),k9_relat_1(sK3,X1))
        | ~ v1_relat_1(sK3) )
    | ~ spl11_8 ),
    inference(resolution,[],[f71,f111])).

fof(f111,plain,
    ( v1_funct_1(sK3)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f110])).

fof(f71,plain,(
    ! [X0,X7,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK6(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK6(X0,X1,X2),X2) )
              & ( ( sK6(X0,X1,X2) = k1_funct_1(X0,sK7(X0,X1,X2))
                  & r2_hidden(sK7(X0,X1,X2),X1)
                  & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK8(X0,X1,X6)) = X6
                    & r2_hidden(sK8(X0,X1,X6),X1)
                    & r2_hidden(sK8(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f26,f29,f28,f27])).

fof(f27,plain,(
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
              ( k1_funct_1(X0,X4) != sK6(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK6(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = sK6(X0,X1,X2)
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( sK6(X0,X1,X2) = k1_funct_1(X0,sK7(X0,X1,X2))
        & r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK8(X0,X1,X6)) = X6
        & r2_hidden(sK8(X0,X1,X6),X1)
        & r2_hidden(sK8(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

fof(f155,plain,
    ( ~ spl11_9
    | ~ spl11_8
    | spl11_16
    | spl11_14 ),
    inference(avatar_split_clause,[],[f150,f144,f153,f110,f115])).

fof(f150,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK5,X0),sK3)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | spl11_14 ),
    inference(resolution,[],[f145,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f145,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK3))
    | spl11_14 ),
    inference(avatar_component_clause,[],[f144])).

fof(f135,plain,
    ( ~ spl11_12
    | spl11_1
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f131,f102,f82,f133])).

fof(f82,plain,
    ( spl11_1
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f131,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | spl11_1
    | ~ spl11_6 ),
    inference(superposition,[],[f83,f130])).

fof(f130,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl11_6 ),
    inference(resolution,[],[f69,f103])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f83,plain,
    ( ~ r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | spl11_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f129,plain,(
    spl11_11 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl11_11 ),
    inference(resolution,[],[f125,f56])).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f125,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl11_11 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl11_11
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f126,plain,
    ( ~ spl11_11
    | ~ spl11_6
    | spl11_9 ),
    inference(avatar_split_clause,[],[f122,f115,f102,f124])).

fof(f122,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl11_6
    | spl11_9 ),
    inference(resolution,[],[f121,f103])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl11_9 ),
    inference(resolution,[],[f116,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f116,plain,
    ( ~ v1_relat_1(sK3)
    | spl11_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f112,plain,(
    spl11_8 ),
    inference(avatar_split_clause,[],[f39,f110])).

fof(f39,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    & sK4 = k1_funct_1(sK3,sK5)
    & r2_hidden(sK5,sK2)
    & r2_hidden(sK5,sK0)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f23,f22,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
            & ? [X5] :
                ( k1_funct_1(X3,X5) = X4
                & r2_hidden(X5,X2)
                & r2_hidden(X5,X0) ) )
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))
          & ? [X5] :
              ( k1_funct_1(sK3,X5) = X4
              & r2_hidden(X5,sK2)
              & r2_hidden(X5,sK0) ) )
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X4] :
        ( ~ r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))
        & ? [X5] :
            ( k1_funct_1(sK3,X5) = X4
            & r2_hidden(X5,sK2)
            & r2_hidden(X5,sK0) ) )
   => ( ~ r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
      & ? [X5] :
          ( k1_funct_1(sK3,X5) = sK4
          & r2_hidden(X5,sK2)
          & r2_hidden(X5,sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X5] :
        ( k1_funct_1(sK3,X5) = sK4
        & r2_hidden(X5,sK2)
        & r2_hidden(X5,sK0) )
   => ( sK4 = k1_funct_1(sK3,sK5)
      & r2_hidden(sK5,sK2)
      & r2_hidden(sK5,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
          & ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
          & ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => ! [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
             => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => ! [X4] :
            ( ? [X5] :
                ( k1_funct_1(X3,X5) = X4
                & r2_hidden(X5,X2)
                & r2_hidden(X5,X0) )
           => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_2)).

fof(f108,plain,(
    spl11_7 ),
    inference(avatar_split_clause,[],[f40,f106])).

fof(f40,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f104,plain,(
    spl11_6 ),
    inference(avatar_split_clause,[],[f41,f102])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f100,plain,(
    ~ spl11_5 ),
    inference(avatar_split_clause,[],[f42,f98])).

fof(f42,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f96,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f43,f94])).

fof(f43,plain,(
    r2_hidden(sK5,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f92,plain,(
    spl11_3 ),
    inference(avatar_split_clause,[],[f44,f90])).

fof(f44,plain,(
    r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f88,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f45,f86])).

fof(f45,plain,(
    sK4 = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f24])).

fof(f84,plain,(
    ~ spl11_1 ),
    inference(avatar_split_clause,[],[f46,f82])).

fof(f46,plain,(
    ~ r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:53:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (5502)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.46  % (5509)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (5498)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.46  % (5509)Refutation not found, incomplete strategy% (5509)------------------------------
% 0.21/0.46  % (5509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (5502)Refutation not found, incomplete strategy% (5502)------------------------------
% 0.21/0.47  % (5502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (5509)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (5509)Memory used [KB]: 10618
% 0.21/0.47  % (5509)Time elapsed: 0.066 s
% 0.21/0.47  % (5509)------------------------------
% 0.21/0.47  % (5509)------------------------------
% 0.21/0.47  % (5503)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (5502)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (5502)Memory used [KB]: 1663
% 0.21/0.47  % (5502)Time elapsed: 0.065 s
% 0.21/0.47  % (5502)------------------------------
% 0.21/0.47  % (5502)------------------------------
% 0.21/0.47  % (5495)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (5491)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (5495)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f197,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f84,f88,f92,f96,f100,f104,f108,f112,f126,f129,f135,f155,f168,f175,f188,f192,f196])).
% 0.21/0.47  fof(f196,plain,(
% 0.21/0.47    ~spl11_3 | spl11_12 | ~spl11_20),
% 0.21/0.47    inference(avatar_split_clause,[],[f194,f190,f133,f90])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    spl11_3 <=> r2_hidden(sK5,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    spl11_12 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 0.21/0.47  fof(f190,plain,(
% 0.21/0.47    spl11_20 <=> ! [X0] : (r2_hidden(sK4,k9_relat_1(sK3,X0)) | ~r2_hidden(sK5,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).
% 0.21/0.47  fof(f194,plain,(
% 0.21/0.47    ~r2_hidden(sK5,sK2) | (spl11_12 | ~spl11_20)),
% 0.21/0.47    inference(resolution,[],[f191,f134])).
% 0.21/0.47  fof(f134,plain,(
% 0.21/0.47    ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | spl11_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f133])).
% 0.21/0.47  fof(f191,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(sK4,k9_relat_1(sK3,X0)) | ~r2_hidden(sK5,X0)) ) | ~spl11_20),
% 0.21/0.47    inference(avatar_component_clause,[],[f190])).
% 0.21/0.47  fof(f192,plain,(
% 0.21/0.47    ~spl11_14 | spl11_20 | ~spl11_2 | ~spl11_18),
% 0.21/0.47    inference(avatar_split_clause,[],[f176,f166,f86,f190,f144])).
% 0.21/0.47  fof(f144,plain,(
% 0.21/0.47    spl11_14 <=> r2_hidden(sK5,k1_relat_1(sK3))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    spl11_2 <=> sK4 = k1_funct_1(sK3,sK5)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 0.21/0.47  fof(f166,plain,(
% 0.21/0.47    spl11_18 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | r2_hidden(k1_funct_1(sK3,X0),k9_relat_1(sK3,X1)) | ~r2_hidden(X0,k1_relat_1(sK3)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).
% 0.21/0.47  fof(f176,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(sK4,k9_relat_1(sK3,X0)) | ~r2_hidden(sK5,X0) | ~r2_hidden(sK5,k1_relat_1(sK3))) ) | (~spl11_2 | ~spl11_18)),
% 0.21/0.47    inference(superposition,[],[f167,f87])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    sK4 = k1_funct_1(sK3,sK5) | ~spl11_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f86])).
% 0.21/0.47  fof(f167,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(k1_funct_1(sK3,X0),k9_relat_1(sK3,X1)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(sK3))) ) | ~spl11_18),
% 0.21/0.47    inference(avatar_component_clause,[],[f166])).
% 0.21/0.47  fof(f188,plain,(
% 0.21/0.47    ~spl11_4 | ~spl11_6 | ~spl11_16 | ~spl11_19),
% 0.21/0.47    inference(avatar_split_clause,[],[f186,f171,f153,f102,f94])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    spl11_4 <=> r2_hidden(sK5,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    spl11_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 0.21/0.47  fof(f153,plain,(
% 0.21/0.47    spl11_16 <=> ! [X0] : ~r2_hidden(k4_tarski(sK5,X0),sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).
% 0.21/0.47  fof(f171,plain,(
% 0.21/0.47    spl11_19 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).
% 0.21/0.47  fof(f186,plain,(
% 0.21/0.47    ~r2_hidden(sK5,sK0) | (~spl11_6 | ~spl11_16 | ~spl11_19)),
% 0.21/0.47    inference(resolution,[],[f184,f154])).
% 0.21/0.47  fof(f154,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(k4_tarski(sK5,X0),sK3)) ) | ~spl11_16),
% 0.21/0.47    inference(avatar_component_clause,[],[f153])).
% 0.21/0.47  fof(f184,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK9(sK3,X0)),sK3) | ~r2_hidden(X0,sK0)) ) | (~spl11_6 | ~spl11_19)),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f183])).
% 0.21/0.47  fof(f183,plain,(
% 0.21/0.47    ( ! [X0] : (sK0 != sK0 | ~r2_hidden(X0,sK0) | r2_hidden(k4_tarski(X0,sK9(sK3,X0)),sK3)) ) | (~spl11_6 | ~spl11_19)),
% 0.21/0.47    inference(forward_demodulation,[],[f182,f172])).
% 0.21/0.47  fof(f172,plain,(
% 0.21/0.47    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl11_19),
% 0.21/0.47    inference(avatar_component_clause,[],[f171])).
% 0.21/0.47  fof(f182,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,sK0) | sK0 != k1_relset_1(sK0,sK1,sK3) | r2_hidden(k4_tarski(X0,sK9(sK3,X0)),sK3)) ) | ~spl11_6),
% 0.21/0.47    inference(resolution,[],[f65,f103])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl11_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f102])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_hidden(X3,X1) | k1_relset_1(X1,X0,X2) != X1 | r2_hidden(k4_tarski(X3,sK9(X2,X3)),X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK9(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK10(X1,X2),X6),X2) & r2_hidden(sK10(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f33,f35,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK9(X2,X3)),X2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK10(X1,X2),X6),X2) & r2_hidden(sK10(X1,X2),X1)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.47    inference(rectify,[],[f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.47    inference(nnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).
% 0.21/0.47  fof(f175,plain,(
% 0.21/0.47    spl11_19 | spl11_5 | ~spl11_7 | ~spl11_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f169,f102,f106,f98,f171])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    spl11_5 <=> k1_xboole_0 = sK1),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    spl11_7 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 0.21/0.47  fof(f169,plain,(
% 0.21/0.47    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl11_6),
% 0.21/0.47    inference(resolution,[],[f57,f103])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(nnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(flattening,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.47  fof(f168,plain,(
% 0.21/0.47    ~spl11_9 | spl11_18 | ~spl11_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f164,f110,f166,f115])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    spl11_9 <=> v1_relat_1(sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    spl11_8 <=> v1_funct_1(sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 0.21/0.47  fof(f164,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k1_funct_1(sK3,X0),k9_relat_1(sK3,X1)) | ~v1_relat_1(sK3)) ) | ~spl11_8),
% 0.21/0.47    inference(resolution,[],[f71,f111])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    v1_funct_1(sK3) | ~spl11_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f110])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ( ! [X0,X7,X1] : (~v1_funct_1(X0) | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f70])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    ( ! [X2,X0,X7,X1] : (r2_hidden(k1_funct_1(X0,X7),X2) | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK6(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((sK6(X0,X1,X2) = k1_funct_1(X0,sK7(X0,X1,X2)) & r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK8(X0,X1,X6)) = X6 & r2_hidden(sK8(X0,X1,X6),X1) & r2_hidden(sK8(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f26,f29,f28,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK6(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK6(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = sK6(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (sK6(X0,X1,X2) = k1_funct_1(X0,sK7(X0,X1,X2)) & r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK8(X0,X1,X6)) = X6 & r2_hidden(sK8(X0,X1,X6),X1) & r2_hidden(sK8(X0,X1,X6),k1_relat_1(X0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(rectify,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    ~spl11_9 | ~spl11_8 | spl11_16 | spl11_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f150,f144,f153,f110,f115])).
% 0.21/0.47  fof(f150,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(k4_tarski(sK5,X0),sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | spl11_14),
% 0.21/0.47    inference(resolution,[],[f145,f66])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(nnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.47  fof(f145,plain,(
% 0.21/0.47    ~r2_hidden(sK5,k1_relat_1(sK3)) | spl11_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f144])).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    ~spl11_12 | spl11_1 | ~spl11_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f131,f102,f82,f133])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    spl11_1 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (spl11_1 | ~spl11_6)),
% 0.21/0.47    inference(superposition,[],[f83,f130])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl11_6),
% 0.21/0.47    inference(resolution,[],[f69,f103])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    ~r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | spl11_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f82])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    spl11_11),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f127])).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    $false | spl11_11),
% 0.21/0.47    inference(resolution,[],[f125,f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl11_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f124])).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    spl11_11 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 0.21/0.47  fof(f126,plain,(
% 0.21/0.47    ~spl11_11 | ~spl11_6 | spl11_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f122,f115,f102,f124])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl11_6 | spl11_9)),
% 0.21/0.47    inference(resolution,[],[f121,f103])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl11_9),
% 0.21/0.47    inference(resolution,[],[f116,f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    ~v1_relat_1(sK3) | spl11_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f115])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    spl11_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f39,f110])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    v1_funct_1(sK3)),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    (~r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) & (sK4 = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK5,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f23,f22,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3] : (? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (~r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) & ? [X5] : (k1_funct_1(sK3,X5) = X4 & r2_hidden(X5,sK2) & r2_hidden(X5,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ? [X4] : (~r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) & ? [X5] : (k1_funct_1(sK3,X5) = X4 & r2_hidden(X5,sK2) & r2_hidden(X5,sK0))) => (~r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) & ? [X5] : (k1_funct_1(sK3,X5) = sK4 & r2_hidden(X5,sK2) & r2_hidden(X5,sK0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ? [X5] : (k1_funct_1(sK3,X5) = sK4 & r2_hidden(X5,sK2) & r2_hidden(X5,sK0)) => (sK4 = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK5,sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3] : (? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.47    inference(flattening,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3] : ((? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)))))),
% 0.21/0.47    inference(negated_conjecture,[],[f8])).
% 0.21/0.47  fof(f8,conjecture,(
% 0.21/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_2)).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    spl11_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f40,f106])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    spl11_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f41,f102])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    ~spl11_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f42,f98])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    k1_xboole_0 != sK1),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    spl11_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f43,f94])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    r2_hidden(sK5,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    spl11_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f44,f90])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    r2_hidden(sK5,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    spl11_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f45,f86])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    sK4 = k1_funct_1(sK3,sK5)),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    ~spl11_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f46,f82])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ~r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (5495)------------------------------
% 0.21/0.47  % (5495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (5495)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (5495)Memory used [KB]: 10746
% 0.21/0.47  % (5495)Time elapsed: 0.028 s
% 0.21/0.47  % (5495)------------------------------
% 0.21/0.47  % (5495)------------------------------
% 0.21/0.48  % (5489)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (5496)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (5488)Success in time 0.126 s
%------------------------------------------------------------------------------
