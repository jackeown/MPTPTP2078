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
% DateTime   : Thu Dec  3 13:05:33 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 363 expanded)
%              Number of leaves         :   32 ( 145 expanded)
%              Depth                    :   13
%              Number of atoms          :  635 (1994 expanded)
%              Number of equality atoms :  161 ( 565 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f404,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f68,f77,f82,f89,f100,f108,f113,f119,f140,f149,f164,f184,f192,f213,f252,f263,f271,f295,f301,f325,f332,f393,f403])).

fof(f403,plain,
    ( ~ spl6_1
    | spl6_3
    | ~ spl6_6
    | ~ spl6_39 ),
    inference(avatar_contradiction_clause,[],[f402])).

fof(f402,plain,
    ( $false
    | ~ spl6_1
    | spl6_3
    | ~ spl6_6
    | ~ spl6_39 ),
    inference(subsumption_resolution,[],[f401,f88])).

fof(f88,plain,
    ( v1_relat_1(sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl6_6
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f401,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl6_1
    | spl6_3
    | ~ spl6_39 ),
    inference(subsumption_resolution,[],[f400,f62])).

fof(f62,plain,
    ( v1_funct_1(sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl6_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f400,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl6_3
    | ~ spl6_39 ),
    inference(subsumption_resolution,[],[f398,f72])).

fof(f72,plain,
    ( ~ v2_funct_1(sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl6_3
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f398,plain,
    ( v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl6_39 ),
    inference(trivial_inequality_removal,[],[f396])).

fof(f396,plain,
    ( sK4(sK1) != sK4(sK1)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl6_39 ),
    inference(superposition,[],[f43,f392])).

fof(f392,plain,
    ( sK4(sK1) = sK5(sK1)
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f390])).

fof(f390,plain,
    ( spl6_39
  <=> sK4(sK1) = sK5(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f43,plain,(
    ! [X0] :
      ( sK4(X0) != sK5(X0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK4(X0) != sK5(X0)
            & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
            & r2_hidden(sK5(X0),k1_relat_1(X0))
            & r2_hidden(sK4(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f26,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK4(X0) != sK5(X0)
        & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
        & r2_hidden(sK5(X0),k1_relat_1(X0))
        & r2_hidden(sK4(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f393,plain,
    ( spl6_39
    | ~ spl6_20
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f386,f267,f210,f390])).

fof(f210,plain,
    ( spl6_20
  <=> r2_hidden(sK4(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f267,plain,
    ( spl6_24
  <=> ! [X0] :
        ( k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,X0)
        | ~ r2_hidden(X0,sK0)
        | sK5(sK1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f386,plain,
    ( sK4(sK1) = sK5(sK1)
    | ~ spl6_20
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f385,f212])).

fof(f212,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f210])).

fof(f385,plain,
    ( ~ r2_hidden(sK4(sK1),sK0)
    | sK4(sK1) = sK5(sK1)
    | ~ spl6_24 ),
    inference(equality_resolution,[],[f268])).

fof(f268,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,X0)
        | ~ r2_hidden(X0,sK0)
        | sK5(sK1) = X0 )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f267])).

fof(f332,plain,
    ( ~ spl6_4
    | ~ spl6_10
    | ~ spl6_11
    | spl6_26
    | ~ spl6_27 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_10
    | ~ spl6_11
    | spl6_26
    | ~ spl6_27 ),
    inference(unit_resulting_resolution,[],[f294,f76,f118,f300,f112])).

fof(f112,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,sK0)
        | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
        | ~ r2_hidden(X5,sK0)
        | X4 = X5 )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl6_10
  <=> ! [X5,X4] :
        ( X4 = X5
        | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
        | ~ r2_hidden(X5,sK0)
        | ~ r2_hidden(X4,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f300,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl6_27
  <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f118,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl6_11
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f76,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl6_4
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f294,plain,
    ( sK2 != sK3
    | spl6_26 ),
    inference(avatar_component_clause,[],[f292])).

fof(f292,plain,
    ( spl6_26
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f325,plain,
    ( spl6_10
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f283,f146,f86,f70,f60,f111])).

fof(f146,plain,
    ( spl6_15
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f283,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X1,sK0)
        | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
        | X0 = X1 )
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_15 ),
    inference(forward_demodulation,[],[f282,f148])).

fof(f148,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f146])).

fof(f282,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK0)
        | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | X0 = X1 )
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_15 ),
    inference(forward_demodulation,[],[f281,f148])).

fof(f281,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
        | ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | X0 = X1 )
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f280,f88])).

fof(f280,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
        | ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | X0 = X1
        | ~ v1_relat_1(sK1) )
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f277,f62])).

fof(f277,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
        | ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | X0 = X1
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl6_3 ),
    inference(resolution,[],[f71,f39])).

fof(f39,plain,(
    ! [X4,X0,X3] :
      ( ~ v2_funct_1(X0)
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | X3 = X4
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,
    ( v2_funct_1(sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f301,plain,
    ( spl6_27
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f296,f70,f298])).

fof(f296,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f36,f71])).

fof(f36,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ( sK2 != sK3
        & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
        & r2_hidden(sK3,sK0)
        & r2_hidden(sK2,sK0) )
      | ~ v2_funct_1(sK1) )
    & ( ! [X4,X5] :
          ( X4 = X5
          | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
          | ~ r2_hidden(X5,sK0)
          | ~ r2_hidden(X4,sK0) )
      | v2_funct_1(sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f23,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ( ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | ~ v2_funct_1(X1) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X0) )
          | v2_funct_1(X1) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ? [X3,X2] :
            ( X2 != X3
            & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
            & r2_hidden(X3,sK0)
            & r2_hidden(X2,sK0) )
        | ~ v2_funct_1(sK1) )
      & ( ! [X5,X4] :
            ( X4 = X5
            | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
            | ~ r2_hidden(X5,sK0)
            | ~ r2_hidden(X4,sK0) )
        | v2_funct_1(sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X3,X2] :
        ( X2 != X3
        & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
        & r2_hidden(X3,sK0)
        & r2_hidden(X2,sK0) )
   => ( sK2 != sK3
      & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
      & r2_hidden(sK3,sK0)
      & r2_hidden(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
            | ~ r2_hidden(X5,X0)
            | ~ r2_hidden(X4,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).

fof(f295,plain,
    ( ~ spl6_26
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f290,f70,f292])).

fof(f290,plain,
    ( sK2 != sK3
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f37,f71])).

fof(f37,plain,
    ( sK2 != sK3
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f271,plain,
    ( spl6_24
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f246,f181,f111,f105,f267])).

fof(f105,plain,
    ( spl6_9
  <=> k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f181,plain,
    ( spl6_18
  <=> r2_hidden(sK5(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f246,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,X0)
        | ~ r2_hidden(X0,sK0)
        | sK5(sK1) = X0 )
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f245,f107])).

fof(f107,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f105])).

fof(f245,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK5(sK1)) != k1_funct_1(sK1,X0)
        | ~ r2_hidden(X0,sK0)
        | sK5(sK1) = X0 )
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(resolution,[],[f183,f112])).

fof(f183,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f181])).

fof(f263,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | k1_relat_1(sK1) != k1_relset_1(sK0,sK0,sK1)
    | sK0 = k1_relat_1(sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f252,plain,
    ( spl6_22
    | ~ spl6_17
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f220,f189,f161,f249])).

fof(f249,plain,
    ( spl6_22
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f161,plain,
    ( spl6_17
  <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f189,plain,
    ( spl6_19
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f220,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | ~ spl6_17
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f214,f163])).

fof(f163,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f161])).

fof(f214,plain,
    ( ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | ~ spl6_19 ),
    inference(resolution,[],[f191,f58])).

fof(f58,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
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
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f18])).

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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f6])).

% (10400)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% (10396)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% (10384)Refutation not found, incomplete strategy% (10384)------------------------------
% (10384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10384)Termination reason: Refutation not found, incomplete strategy

% (10384)Memory used [KB]: 10618
% (10384)Time elapsed: 0.107 s
% (10384)------------------------------
% (10384)------------------------------
% (10383)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% (10390)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% (10392)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f6,axiom,(
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

fof(f191,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f189])).

fof(f213,plain,
    ( spl6_20
    | ~ spl6_1
    | spl6_3
    | ~ spl6_6
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f206,f146,f86,f70,f60,f210])).

fof(f206,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | ~ spl6_1
    | spl6_3
    | ~ spl6_6
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f205,f88])).

fof(f205,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl6_1
    | spl6_3
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f204,f62])).

fof(f204,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl6_3
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f200,f72])).

fof(f200,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl6_15 ),
    inference(superposition,[],[f40,f148])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f192,plain,
    ( spl6_19
    | ~ spl6_5
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f185,f137,f79,f189])).

fof(f79,plain,
    ( spl6_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f137,plain,
    ( spl6_14
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f185,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_5
    | ~ spl6_14 ),
    inference(backward_demodulation,[],[f81,f139])).

fof(f139,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f137])).

fof(f81,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f184,plain,
    ( spl6_18
    | ~ spl6_1
    | spl6_3
    | ~ spl6_6
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f169,f146,f86,f70,f60,f181])).

fof(f169,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | ~ spl6_1
    | spl6_3
    | ~ spl6_6
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f168,f88])).

fof(f168,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl6_1
    | spl6_3
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f167,f62])).

fof(f167,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl6_3
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f165,f72])).

fof(f165,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl6_15 ),
    inference(superposition,[],[f41,f148])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f164,plain,
    ( spl6_17
    | ~ spl6_2
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f153,f137,f65,f161])).

fof(f65,plain,
    ( spl6_2
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f153,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_14 ),
    inference(backward_demodulation,[],[f67,f139])).

fof(f67,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f149,plain,
    ( spl6_15
    | ~ spl6_8
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f142,f133,f97,f146])).

fof(f97,plain,
    ( spl6_8
  <=> k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f133,plain,
    ( spl6_13
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f142,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl6_8
    | ~ spl6_13 ),
    inference(backward_demodulation,[],[f99,f135])).

fof(f135,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f133])).

fof(f99,plain,
    ( k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f97])).

fof(f140,plain,
    ( spl6_13
    | spl6_14
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f131,f79,f65,f137,f133])).

fof(f131,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f130,f67])).

fof(f130,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | k1_xboole_0 = sK0
    | sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl6_5 ),
    inference(resolution,[],[f48,f81])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f119,plain,
    ( spl6_11
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f114,f70,f116])).

fof(f114,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f35,f71])).

fof(f35,plain,
    ( r2_hidden(sK3,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f113,plain,
    ( spl6_10
    | spl6_3 ),
    inference(avatar_split_clause,[],[f109,f70,f111])).

fof(f109,plain,
    ( ! [X4,X5] :
        ( X4 = X5
        | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
        | ~ r2_hidden(X5,sK0)
        | ~ r2_hidden(X4,sK0) )
    | spl6_3 ),
    inference(subsumption_resolution,[],[f33,f72])).

fof(f33,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
      | ~ r2_hidden(X5,sK0)
      | ~ r2_hidden(X4,sK0)
      | v2_funct_1(sK1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f108,plain,
    ( spl6_9
    | ~ spl6_1
    | spl6_3
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f103,f86,f70,f60,f105])).

fof(f103,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ spl6_1
    | spl6_3
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f102,f88])).

fof(f102,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl6_1
    | spl6_3 ),
    inference(subsumption_resolution,[],[f101,f62])).

fof(f101,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl6_3 ),
    inference(resolution,[],[f42,f72])).

fof(f42,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f100,plain,
    ( spl6_8
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f95,f79,f97])).

fof(f95,plain,
    ( k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)
    | ~ spl6_5 ),
    inference(resolution,[],[f47,f81])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f89,plain,
    ( spl6_6
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f84,f79,f86])).

fof(f84,plain,
    ( v1_relat_1(sK1)
    | ~ spl6_5 ),
    inference(resolution,[],[f83,f81])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f38,f44])).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f82,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f32,f79])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f77,plain,
    ( ~ spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f34,f74,f70])).

fof(f34,plain,
    ( r2_hidden(sK2,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f68,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f31,f65])).

fof(f31,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f30,f60])).

fof(f30,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:43:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.47  % (10402)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.48  % (10394)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.50  % (10387)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.50  % (10384)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (10385)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.51  % (10385)Refutation not found, incomplete strategy% (10385)------------------------------
% 0.20/0.51  % (10385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (10385)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (10385)Memory used [KB]: 1663
% 0.20/0.51  % (10385)Time elapsed: 0.091 s
% 0.20/0.51  % (10385)------------------------------
% 0.20/0.51  % (10385)------------------------------
% 0.20/0.51  % (10379)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.20/0.51  % (10378)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.20/0.51  % (10382)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.20/0.51  % (10388)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.20/0.51  % (10378)Refutation not found, incomplete strategy% (10378)------------------------------
% 1.20/0.51  % (10378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.51  % (10380)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.20/0.51  % (10378)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.51  
% 1.20/0.51  % (10378)Memory used [KB]: 10618
% 1.20/0.51  % (10378)Time elapsed: 0.102 s
% 1.20/0.51  % (10378)------------------------------
% 1.20/0.51  % (10378)------------------------------
% 1.20/0.52  % (10395)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.20/0.52  % (10386)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.20/0.52  % (10393)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.20/0.52  % (10380)Refutation found. Thanks to Tanya!
% 1.20/0.52  % SZS status Theorem for theBenchmark
% 1.20/0.52  % SZS output start Proof for theBenchmark
% 1.20/0.52  fof(f404,plain,(
% 1.20/0.52    $false),
% 1.20/0.52    inference(avatar_sat_refutation,[],[f63,f68,f77,f82,f89,f100,f108,f113,f119,f140,f149,f164,f184,f192,f213,f252,f263,f271,f295,f301,f325,f332,f393,f403])).
% 1.20/0.52  fof(f403,plain,(
% 1.20/0.52    ~spl6_1 | spl6_3 | ~spl6_6 | ~spl6_39),
% 1.20/0.52    inference(avatar_contradiction_clause,[],[f402])).
% 1.20/0.52  fof(f402,plain,(
% 1.20/0.52    $false | (~spl6_1 | spl6_3 | ~spl6_6 | ~spl6_39)),
% 1.20/0.52    inference(subsumption_resolution,[],[f401,f88])).
% 1.20/0.52  fof(f88,plain,(
% 1.20/0.52    v1_relat_1(sK1) | ~spl6_6),
% 1.20/0.52    inference(avatar_component_clause,[],[f86])).
% 1.20/0.52  fof(f86,plain,(
% 1.20/0.52    spl6_6 <=> v1_relat_1(sK1)),
% 1.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.20/0.52  fof(f401,plain,(
% 1.20/0.52    ~v1_relat_1(sK1) | (~spl6_1 | spl6_3 | ~spl6_39)),
% 1.20/0.52    inference(subsumption_resolution,[],[f400,f62])).
% 1.20/0.52  fof(f62,plain,(
% 1.20/0.52    v1_funct_1(sK1) | ~spl6_1),
% 1.20/0.52    inference(avatar_component_clause,[],[f60])).
% 1.20/0.52  fof(f60,plain,(
% 1.20/0.52    spl6_1 <=> v1_funct_1(sK1)),
% 1.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.20/0.52  fof(f400,plain,(
% 1.20/0.52    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (spl6_3 | ~spl6_39)),
% 1.20/0.52    inference(subsumption_resolution,[],[f398,f72])).
% 1.20/0.52  fof(f72,plain,(
% 1.20/0.52    ~v2_funct_1(sK1) | spl6_3),
% 1.20/0.52    inference(avatar_component_clause,[],[f70])).
% 1.20/0.52  fof(f70,plain,(
% 1.20/0.52    spl6_3 <=> v2_funct_1(sK1)),
% 1.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.20/0.52  fof(f398,plain,(
% 1.20/0.52    v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl6_39),
% 1.20/0.52    inference(trivial_inequality_removal,[],[f396])).
% 1.20/0.52  fof(f396,plain,(
% 1.20/0.52    sK4(sK1) != sK4(sK1) | v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl6_39),
% 1.20/0.52    inference(superposition,[],[f43,f392])).
% 1.20/0.52  fof(f392,plain,(
% 1.20/0.52    sK4(sK1) = sK5(sK1) | ~spl6_39),
% 1.20/0.52    inference(avatar_component_clause,[],[f390])).
% 1.20/0.52  fof(f390,plain,(
% 1.20/0.52    spl6_39 <=> sK4(sK1) = sK5(sK1)),
% 1.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 1.20/0.52  fof(f43,plain,(
% 1.20/0.52    ( ! [X0] : (sK4(X0) != sK5(X0) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f28])).
% 1.20/0.52  fof(f28,plain,(
% 1.20/0.52    ! [X0] : (((v2_funct_1(X0) | (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f26,f27])).
% 1.20/0.52  fof(f27,plain,(
% 1.20/0.52    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0))))),
% 1.20/0.52    introduced(choice_axiom,[])).
% 1.20/0.52  fof(f26,plain,(
% 1.20/0.52    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.20/0.52    inference(rectify,[],[f25])).
% 1.20/0.52  fof(f25,plain,(
% 1.20/0.52    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.20/0.52    inference(nnf_transformation,[],[f13])).
% 1.20/0.52  fof(f13,plain,(
% 1.20/0.52    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.20/0.52    inference(flattening,[],[f12])).
% 1.20/0.52  fof(f12,plain,(
% 1.20/0.52    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.20/0.52    inference(ennf_transformation,[],[f3])).
% 1.20/0.52  fof(f3,axiom,(
% 1.20/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 1.20/0.52  fof(f393,plain,(
% 1.20/0.52    spl6_39 | ~spl6_20 | ~spl6_24),
% 1.20/0.52    inference(avatar_split_clause,[],[f386,f267,f210,f390])).
% 1.20/0.52  fof(f210,plain,(
% 1.20/0.52    spl6_20 <=> r2_hidden(sK4(sK1),sK0)),
% 1.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 1.20/0.52  fof(f267,plain,(
% 1.20/0.52    spl6_24 <=> ! [X0] : (k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,X0) | ~r2_hidden(X0,sK0) | sK5(sK1) = X0)),
% 1.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.20/0.52  fof(f386,plain,(
% 1.20/0.52    sK4(sK1) = sK5(sK1) | (~spl6_20 | ~spl6_24)),
% 1.20/0.52    inference(subsumption_resolution,[],[f385,f212])).
% 1.20/0.52  fof(f212,plain,(
% 1.20/0.52    r2_hidden(sK4(sK1),sK0) | ~spl6_20),
% 1.20/0.52    inference(avatar_component_clause,[],[f210])).
% 1.20/0.52  fof(f385,plain,(
% 1.20/0.52    ~r2_hidden(sK4(sK1),sK0) | sK4(sK1) = sK5(sK1) | ~spl6_24),
% 1.20/0.52    inference(equality_resolution,[],[f268])).
% 1.20/0.52  fof(f268,plain,(
% 1.20/0.52    ( ! [X0] : (k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,X0) | ~r2_hidden(X0,sK0) | sK5(sK1) = X0) ) | ~spl6_24),
% 1.20/0.52    inference(avatar_component_clause,[],[f267])).
% 1.20/0.52  fof(f332,plain,(
% 1.20/0.52    ~spl6_4 | ~spl6_10 | ~spl6_11 | spl6_26 | ~spl6_27),
% 1.20/0.52    inference(avatar_contradiction_clause,[],[f327])).
% 1.20/0.52  fof(f327,plain,(
% 1.20/0.52    $false | (~spl6_4 | ~spl6_10 | ~spl6_11 | spl6_26 | ~spl6_27)),
% 1.20/0.52    inference(unit_resulting_resolution,[],[f294,f76,f118,f300,f112])).
% 1.20/0.52  fof(f112,plain,(
% 1.20/0.52    ( ! [X4,X5] : (~r2_hidden(X4,sK0) | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | X4 = X5) ) | ~spl6_10),
% 1.20/0.52    inference(avatar_component_clause,[],[f111])).
% 1.20/0.52  fof(f111,plain,(
% 1.20/0.52    spl6_10 <=> ! [X5,X4] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0))),
% 1.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.20/0.52  fof(f300,plain,(
% 1.20/0.52    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~spl6_27),
% 1.20/0.52    inference(avatar_component_clause,[],[f298])).
% 1.20/0.52  fof(f298,plain,(
% 1.20/0.52    spl6_27 <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 1.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 1.20/0.52  fof(f118,plain,(
% 1.20/0.52    r2_hidden(sK3,sK0) | ~spl6_11),
% 1.20/0.52    inference(avatar_component_clause,[],[f116])).
% 1.20/0.52  fof(f116,plain,(
% 1.20/0.52    spl6_11 <=> r2_hidden(sK3,sK0)),
% 1.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.20/0.52  fof(f76,plain,(
% 1.20/0.52    r2_hidden(sK2,sK0) | ~spl6_4),
% 1.20/0.52    inference(avatar_component_clause,[],[f74])).
% 1.20/0.52  fof(f74,plain,(
% 1.20/0.52    spl6_4 <=> r2_hidden(sK2,sK0)),
% 1.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.20/0.52  fof(f294,plain,(
% 1.20/0.52    sK2 != sK3 | spl6_26),
% 1.20/0.52    inference(avatar_component_clause,[],[f292])).
% 1.20/0.52  fof(f292,plain,(
% 1.20/0.52    spl6_26 <=> sK2 = sK3),
% 1.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 1.20/0.52  fof(f325,plain,(
% 1.20/0.52    spl6_10 | ~spl6_1 | ~spl6_3 | ~spl6_6 | ~spl6_15),
% 1.20/0.52    inference(avatar_split_clause,[],[f283,f146,f86,f70,f60,f111])).
% 1.20/0.52  fof(f146,plain,(
% 1.20/0.52    spl6_15 <=> sK0 = k1_relat_1(sK1)),
% 1.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.20/0.52  fof(f283,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~r2_hidden(X1,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1) ) | (~spl6_1 | ~spl6_3 | ~spl6_6 | ~spl6_15)),
% 1.20/0.52    inference(forward_demodulation,[],[f282,f148])).
% 1.20/0.52  fof(f148,plain,(
% 1.20/0.52    sK0 = k1_relat_1(sK1) | ~spl6_15),
% 1.20/0.52    inference(avatar_component_clause,[],[f146])).
% 1.20/0.52  fof(f282,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~r2_hidden(X1,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | ~r2_hidden(X0,k1_relat_1(sK1)) | X0 = X1) ) | (~spl6_1 | ~spl6_3 | ~spl6_6 | ~spl6_15)),
% 1.20/0.52    inference(forward_demodulation,[],[f281,f148])).
% 1.20/0.52  fof(f281,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | ~r2_hidden(X1,k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK1)) | X0 = X1) ) | (~spl6_1 | ~spl6_3 | ~spl6_6)),
% 1.20/0.52    inference(subsumption_resolution,[],[f280,f88])).
% 1.20/0.52  fof(f280,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | ~r2_hidden(X1,k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK1)) | X0 = X1 | ~v1_relat_1(sK1)) ) | (~spl6_1 | ~spl6_3)),
% 1.20/0.52    inference(subsumption_resolution,[],[f277,f62])).
% 1.20/0.52  fof(f277,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | ~r2_hidden(X1,k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK1)) | X0 = X1 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | ~spl6_3),
% 1.20/0.52    inference(resolution,[],[f71,f39])).
% 1.20/0.52  fof(f39,plain,(
% 1.20/0.52    ( ! [X4,X0,X3] : (~v2_funct_1(X0) | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | X3 = X4 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f28])).
% 1.20/0.52  fof(f71,plain,(
% 1.20/0.52    v2_funct_1(sK1) | ~spl6_3),
% 1.20/0.52    inference(avatar_component_clause,[],[f70])).
% 1.20/0.52  fof(f301,plain,(
% 1.20/0.52    spl6_27 | ~spl6_3),
% 1.20/0.52    inference(avatar_split_clause,[],[f296,f70,f298])).
% 1.20/0.52  fof(f296,plain,(
% 1.20/0.52    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~spl6_3),
% 1.20/0.52    inference(subsumption_resolution,[],[f36,f71])).
% 1.20/0.52  fof(f36,plain,(
% 1.20/0.52    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~v2_funct_1(sK1)),
% 1.20/0.52    inference(cnf_transformation,[],[f24])).
% 1.20/0.52  fof(f24,plain,(
% 1.20/0.52    ((sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0)) | ~v2_funct_1(sK1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0)) | v2_funct_1(sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 1.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f23,f22])).
% 1.20/0.52  fof(f22,plain,(
% 1.20/0.52    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) | ~v2_funct_1(sK1)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0)) | v2_funct_1(sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.20/0.52    introduced(choice_axiom,[])).
% 1.20/0.52  fof(f23,plain,(
% 1.20/0.52    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) => (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0))),
% 1.20/0.52    introduced(choice_axiom,[])).
% 1.20/0.52  fof(f21,plain,(
% 1.20/0.52    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.20/0.52    inference(rectify,[],[f20])).
% 1.20/0.52  fof(f20,plain,(
% 1.20/0.52    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.20/0.52    inference(flattening,[],[f19])).
% 1.20/0.52  fof(f19,plain,(
% 1.20/0.52    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.20/0.52    inference(nnf_transformation,[],[f10])).
% 1.20/0.52  fof(f10,plain,(
% 1.20/0.52    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.20/0.52    inference(flattening,[],[f9])).
% 1.20/0.52  fof(f9,plain,(
% 1.20/0.52    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.20/0.52    inference(ennf_transformation,[],[f8])).
% 1.20/0.52  fof(f8,negated_conjecture,(
% 1.20/0.52    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 1.20/0.52    inference(negated_conjecture,[],[f7])).
% 1.20/0.52  fof(f7,conjecture,(
% 1.20/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).
% 1.20/0.52  fof(f295,plain,(
% 1.20/0.52    ~spl6_26 | ~spl6_3),
% 1.20/0.52    inference(avatar_split_clause,[],[f290,f70,f292])).
% 1.20/0.52  fof(f290,plain,(
% 1.20/0.52    sK2 != sK3 | ~spl6_3),
% 1.20/0.52    inference(subsumption_resolution,[],[f37,f71])).
% 1.20/0.52  fof(f37,plain,(
% 1.20/0.52    sK2 != sK3 | ~v2_funct_1(sK1)),
% 1.20/0.52    inference(cnf_transformation,[],[f24])).
% 1.20/0.52  fof(f271,plain,(
% 1.20/0.52    spl6_24 | ~spl6_9 | ~spl6_10 | ~spl6_18),
% 1.20/0.52    inference(avatar_split_clause,[],[f246,f181,f111,f105,f267])).
% 1.20/0.52  fof(f105,plain,(
% 1.20/0.52    spl6_9 <=> k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))),
% 1.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.20/0.52  fof(f181,plain,(
% 1.20/0.52    spl6_18 <=> r2_hidden(sK5(sK1),sK0)),
% 1.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.20/0.52  fof(f246,plain,(
% 1.20/0.52    ( ! [X0] : (k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,X0) | ~r2_hidden(X0,sK0) | sK5(sK1) = X0) ) | (~spl6_9 | ~spl6_10 | ~spl6_18)),
% 1.20/0.52    inference(forward_demodulation,[],[f245,f107])).
% 1.20/0.52  fof(f107,plain,(
% 1.20/0.52    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~spl6_9),
% 1.20/0.52    inference(avatar_component_clause,[],[f105])).
% 1.20/0.52  fof(f245,plain,(
% 1.20/0.52    ( ! [X0] : (k1_funct_1(sK1,sK5(sK1)) != k1_funct_1(sK1,X0) | ~r2_hidden(X0,sK0) | sK5(sK1) = X0) ) | (~spl6_10 | ~spl6_18)),
% 1.20/0.52    inference(resolution,[],[f183,f112])).
% 1.20/0.52  fof(f183,plain,(
% 1.20/0.52    r2_hidden(sK5(sK1),sK0) | ~spl6_18),
% 1.20/0.52    inference(avatar_component_clause,[],[f181])).
% 1.20/0.52  fof(f263,plain,(
% 1.20/0.52    k1_xboole_0 != sK0 | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | k1_relat_1(sK1) != k1_relset_1(sK0,sK0,sK1) | sK0 = k1_relat_1(sK1)),
% 1.20/0.52    introduced(theory_tautology_sat_conflict,[])).
% 1.20/0.52  fof(f252,plain,(
% 1.20/0.52    spl6_22 | ~spl6_17 | ~spl6_19),
% 1.20/0.52    inference(avatar_split_clause,[],[f220,f189,f161,f249])).
% 1.20/0.52  fof(f249,plain,(
% 1.20/0.52    spl6_22 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)),
% 1.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.20/0.52  fof(f161,plain,(
% 1.20/0.52    spl6_17 <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 1.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.20/0.52  fof(f189,plain,(
% 1.20/0.52    spl6_19 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 1.20/0.52  fof(f220,plain,(
% 1.20/0.52    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | (~spl6_17 | ~spl6_19)),
% 1.20/0.52    inference(subsumption_resolution,[],[f214,f163])).
% 1.20/0.52  fof(f163,plain,(
% 1.20/0.52    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~spl6_17),
% 1.20/0.52    inference(avatar_component_clause,[],[f161])).
% 1.20/0.52  fof(f214,plain,(
% 1.20/0.52    ~v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | ~spl6_19),
% 1.20/0.52    inference(resolution,[],[f191,f58])).
% 1.20/0.52  fof(f58,plain,(
% 1.20/0.52    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 1.20/0.52    inference(equality_resolution,[],[f49])).
% 1.20/0.52  fof(f49,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.20/0.52    inference(cnf_transformation,[],[f29])).
% 1.20/0.52  fof(f29,plain,(
% 1.20/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.20/0.52    inference(nnf_transformation,[],[f18])).
% 1.20/0.52  fof(f18,plain,(
% 1.20/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.20/0.52    inference(flattening,[],[f17])).
% 1.20/0.52  fof(f17,plain,(
% 1.20/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.20/0.52    inference(ennf_transformation,[],[f6])).
% 1.20/0.52  % (10400)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.20/0.52  % (10396)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.20/0.52  % (10384)Refutation not found, incomplete strategy% (10384)------------------------------
% 1.20/0.52  % (10384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (10384)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.52  
% 1.20/0.52  % (10384)Memory used [KB]: 10618
% 1.20/0.52  % (10384)Time elapsed: 0.107 s
% 1.20/0.52  % (10384)------------------------------
% 1.20/0.52  % (10384)------------------------------
% 1.20/0.52  % (10383)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.20/0.53  % (10390)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.20/0.53  % (10392)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.20/0.53  fof(f6,axiom,(
% 1.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.20/0.53  fof(f191,plain,(
% 1.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl6_19),
% 1.20/0.53    inference(avatar_component_clause,[],[f189])).
% 1.20/0.53  fof(f213,plain,(
% 1.20/0.53    spl6_20 | ~spl6_1 | spl6_3 | ~spl6_6 | ~spl6_15),
% 1.20/0.53    inference(avatar_split_clause,[],[f206,f146,f86,f70,f60,f210])).
% 1.20/0.53  fof(f206,plain,(
% 1.20/0.53    r2_hidden(sK4(sK1),sK0) | (~spl6_1 | spl6_3 | ~spl6_6 | ~spl6_15)),
% 1.20/0.53    inference(subsumption_resolution,[],[f205,f88])).
% 1.20/0.53  fof(f205,plain,(
% 1.20/0.53    r2_hidden(sK4(sK1),sK0) | ~v1_relat_1(sK1) | (~spl6_1 | spl6_3 | ~spl6_15)),
% 1.20/0.53    inference(subsumption_resolution,[],[f204,f62])).
% 1.20/0.53  fof(f204,plain,(
% 1.20/0.53    r2_hidden(sK4(sK1),sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (spl6_3 | ~spl6_15)),
% 1.20/0.53    inference(subsumption_resolution,[],[f200,f72])).
% 1.20/0.53  fof(f200,plain,(
% 1.20/0.53    r2_hidden(sK4(sK1),sK0) | v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl6_15),
% 1.20/0.53    inference(superposition,[],[f40,f148])).
% 1.20/0.53  fof(f40,plain,(
% 1.20/0.53    ( ! [X0] : (r2_hidden(sK4(X0),k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f28])).
% 1.20/0.53  fof(f192,plain,(
% 1.20/0.53    spl6_19 | ~spl6_5 | ~spl6_14),
% 1.20/0.53    inference(avatar_split_clause,[],[f185,f137,f79,f189])).
% 1.20/0.53  fof(f79,plain,(
% 1.20/0.53    spl6_5 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.20/0.53  fof(f137,plain,(
% 1.20/0.53    spl6_14 <=> k1_xboole_0 = sK0),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.20/0.53  fof(f185,plain,(
% 1.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl6_5 | ~spl6_14)),
% 1.20/0.53    inference(backward_demodulation,[],[f81,f139])).
% 1.20/0.53  fof(f139,plain,(
% 1.20/0.53    k1_xboole_0 = sK0 | ~spl6_14),
% 1.20/0.53    inference(avatar_component_clause,[],[f137])).
% 1.20/0.53  fof(f81,plain,(
% 1.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl6_5),
% 1.20/0.53    inference(avatar_component_clause,[],[f79])).
% 1.20/0.53  fof(f184,plain,(
% 1.20/0.53    spl6_18 | ~spl6_1 | spl6_3 | ~spl6_6 | ~spl6_15),
% 1.20/0.53    inference(avatar_split_clause,[],[f169,f146,f86,f70,f60,f181])).
% 1.20/0.53  fof(f169,plain,(
% 1.20/0.53    r2_hidden(sK5(sK1),sK0) | (~spl6_1 | spl6_3 | ~spl6_6 | ~spl6_15)),
% 1.20/0.53    inference(subsumption_resolution,[],[f168,f88])).
% 1.20/0.53  fof(f168,plain,(
% 1.20/0.53    r2_hidden(sK5(sK1),sK0) | ~v1_relat_1(sK1) | (~spl6_1 | spl6_3 | ~spl6_15)),
% 1.20/0.53    inference(subsumption_resolution,[],[f167,f62])).
% 1.20/0.53  fof(f167,plain,(
% 1.20/0.53    r2_hidden(sK5(sK1),sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (spl6_3 | ~spl6_15)),
% 1.20/0.53    inference(subsumption_resolution,[],[f165,f72])).
% 1.20/0.53  fof(f165,plain,(
% 1.20/0.53    r2_hidden(sK5(sK1),sK0) | v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl6_15),
% 1.20/0.53    inference(superposition,[],[f41,f148])).
% 1.20/0.53  fof(f41,plain,(
% 1.20/0.53    ( ! [X0] : (r2_hidden(sK5(X0),k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f28])).
% 1.20/0.53  fof(f164,plain,(
% 1.20/0.53    spl6_17 | ~spl6_2 | ~spl6_14),
% 1.20/0.53    inference(avatar_split_clause,[],[f153,f137,f65,f161])).
% 1.20/0.53  fof(f65,plain,(
% 1.20/0.53    spl6_2 <=> v1_funct_2(sK1,sK0,sK0)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.20/0.53  fof(f153,plain,(
% 1.20/0.53    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (~spl6_2 | ~spl6_14)),
% 1.20/0.53    inference(backward_demodulation,[],[f67,f139])).
% 1.20/0.53  fof(f67,plain,(
% 1.20/0.53    v1_funct_2(sK1,sK0,sK0) | ~spl6_2),
% 1.20/0.53    inference(avatar_component_clause,[],[f65])).
% 1.20/0.53  fof(f149,plain,(
% 1.20/0.53    spl6_15 | ~spl6_8 | ~spl6_13),
% 1.20/0.53    inference(avatar_split_clause,[],[f142,f133,f97,f146])).
% 1.20/0.53  fof(f97,plain,(
% 1.20/0.53    spl6_8 <=> k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.20/0.53  fof(f133,plain,(
% 1.20/0.53    spl6_13 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.20/0.53  fof(f142,plain,(
% 1.20/0.53    sK0 = k1_relat_1(sK1) | (~spl6_8 | ~spl6_13)),
% 1.20/0.53    inference(backward_demodulation,[],[f99,f135])).
% 1.20/0.53  fof(f135,plain,(
% 1.20/0.53    sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl6_13),
% 1.20/0.53    inference(avatar_component_clause,[],[f133])).
% 1.20/0.53  fof(f99,plain,(
% 1.20/0.53    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) | ~spl6_8),
% 1.20/0.53    inference(avatar_component_clause,[],[f97])).
% 1.20/0.53  fof(f140,plain,(
% 1.20/0.53    spl6_13 | spl6_14 | ~spl6_2 | ~spl6_5),
% 1.20/0.53    inference(avatar_split_clause,[],[f131,f79,f65,f137,f133])).
% 1.20/0.53  fof(f131,plain,(
% 1.20/0.53    k1_xboole_0 = sK0 | sK0 = k1_relset_1(sK0,sK0,sK1) | (~spl6_2 | ~spl6_5)),
% 1.20/0.53    inference(subsumption_resolution,[],[f130,f67])).
% 1.20/0.53  fof(f130,plain,(
% 1.20/0.53    ~v1_funct_2(sK1,sK0,sK0) | k1_xboole_0 = sK0 | sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl6_5),
% 1.20/0.53    inference(resolution,[],[f48,f81])).
% 1.20/0.53  fof(f48,plain,(
% 1.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.20/0.53    inference(cnf_transformation,[],[f29])).
% 1.20/0.53  fof(f119,plain,(
% 1.20/0.53    spl6_11 | ~spl6_3),
% 1.20/0.53    inference(avatar_split_clause,[],[f114,f70,f116])).
% 1.20/0.53  fof(f114,plain,(
% 1.20/0.53    r2_hidden(sK3,sK0) | ~spl6_3),
% 1.20/0.53    inference(subsumption_resolution,[],[f35,f71])).
% 1.20/0.53  fof(f35,plain,(
% 1.20/0.53    r2_hidden(sK3,sK0) | ~v2_funct_1(sK1)),
% 1.20/0.53    inference(cnf_transformation,[],[f24])).
% 1.20/0.53  fof(f113,plain,(
% 1.20/0.53    spl6_10 | spl6_3),
% 1.20/0.53    inference(avatar_split_clause,[],[f109,f70,f111])).
% 1.20/0.53  fof(f109,plain,(
% 1.20/0.53    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0)) ) | spl6_3),
% 1.20/0.53    inference(subsumption_resolution,[],[f33,f72])).
% 1.20/0.53  fof(f33,plain,(
% 1.20/0.53    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0) | v2_funct_1(sK1)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f24])).
% 1.20/0.53  fof(f108,plain,(
% 1.20/0.53    spl6_9 | ~spl6_1 | spl6_3 | ~spl6_6),
% 1.20/0.53    inference(avatar_split_clause,[],[f103,f86,f70,f60,f105])).
% 1.20/0.53  fof(f103,plain,(
% 1.20/0.53    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | (~spl6_1 | spl6_3 | ~spl6_6)),
% 1.20/0.53    inference(subsumption_resolution,[],[f102,f88])).
% 1.20/0.53  fof(f102,plain,(
% 1.20/0.53    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~v1_relat_1(sK1) | (~spl6_1 | spl6_3)),
% 1.20/0.53    inference(subsumption_resolution,[],[f101,f62])).
% 1.20/0.53  fof(f101,plain,(
% 1.20/0.53    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl6_3),
% 1.20/0.53    inference(resolution,[],[f42,f72])).
% 1.20/0.53  fof(f42,plain,(
% 1.20/0.53    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f28])).
% 1.20/0.53  fof(f100,plain,(
% 1.20/0.53    spl6_8 | ~spl6_5),
% 1.20/0.53    inference(avatar_split_clause,[],[f95,f79,f97])).
% 1.20/0.53  fof(f95,plain,(
% 1.20/0.53    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) | ~spl6_5),
% 1.20/0.53    inference(resolution,[],[f47,f81])).
% 1.20/0.53  fof(f47,plain,(
% 1.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f16])).
% 1.20/0.53  fof(f16,plain,(
% 1.20/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.20/0.53    inference(ennf_transformation,[],[f5])).
% 1.20/0.53  fof(f5,axiom,(
% 1.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.20/0.53  fof(f89,plain,(
% 1.20/0.53    spl6_6 | ~spl6_5),
% 1.20/0.53    inference(avatar_split_clause,[],[f84,f79,f86])).
% 1.20/0.53  fof(f84,plain,(
% 1.20/0.53    v1_relat_1(sK1) | ~spl6_5),
% 1.20/0.53    inference(resolution,[],[f83,f81])).
% 1.20/0.53  fof(f83,plain,(
% 1.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 1.20/0.53    inference(resolution,[],[f38,f44])).
% 1.20/0.53  fof(f44,plain,(
% 1.20/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.20/0.53    inference(cnf_transformation,[],[f2])).
% 1.20/0.53  fof(f2,axiom,(
% 1.20/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.20/0.53  fof(f38,plain,(
% 1.20/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f11])).
% 1.20/0.53  fof(f11,plain,(
% 1.20/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.20/0.53    inference(ennf_transformation,[],[f1])).
% 1.20/0.53  fof(f1,axiom,(
% 1.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.20/0.53  fof(f82,plain,(
% 1.20/0.53    spl6_5),
% 1.20/0.53    inference(avatar_split_clause,[],[f32,f79])).
% 1.20/0.53  fof(f32,plain,(
% 1.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.20/0.53    inference(cnf_transformation,[],[f24])).
% 1.20/0.53  fof(f77,plain,(
% 1.20/0.53    ~spl6_3 | spl6_4),
% 1.20/0.53    inference(avatar_split_clause,[],[f34,f74,f70])).
% 1.20/0.53  fof(f34,plain,(
% 1.20/0.53    r2_hidden(sK2,sK0) | ~v2_funct_1(sK1)),
% 1.20/0.53    inference(cnf_transformation,[],[f24])).
% 1.20/0.53  fof(f68,plain,(
% 1.20/0.53    spl6_2),
% 1.20/0.53    inference(avatar_split_clause,[],[f31,f65])).
% 1.20/0.53  fof(f31,plain,(
% 1.20/0.53    v1_funct_2(sK1,sK0,sK0)),
% 1.20/0.53    inference(cnf_transformation,[],[f24])).
% 1.20/0.53  fof(f63,plain,(
% 1.20/0.53    spl6_1),
% 1.20/0.53    inference(avatar_split_clause,[],[f30,f60])).
% 1.20/0.53  fof(f30,plain,(
% 1.20/0.53    v1_funct_1(sK1)),
% 1.20/0.53    inference(cnf_transformation,[],[f24])).
% 1.20/0.53  % SZS output end Proof for theBenchmark
% 1.20/0.53  % (10380)------------------------------
% 1.20/0.53  % (10380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.53  % (10398)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.20/0.53  % (10380)Termination reason: Refutation
% 1.20/0.53  
% 1.20/0.53  % (10380)Memory used [KB]: 6396
% 1.20/0.53  % (10380)Time elapsed: 0.109 s
% 1.20/0.53  % (10380)------------------------------
% 1.20/0.53  % (10380)------------------------------
% 1.20/0.53  % (10377)Success in time 0.169 s
%------------------------------------------------------------------------------
