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
% DateTime   : Thu Dec  3 12:53:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 177 expanded)
%              Number of leaves         :   24 (  80 expanded)
%              Depth                    :    7
%              Number of atoms          :  311 ( 812 expanded)
%              Number of equality atoms :   85 ( 264 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f376,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f54,f58,f62,f70,f74,f78,f92,f100,f102,f280,f353,f363,f370,f375])).

fof(f375,plain,
    ( ~ spl2_6
    | spl2_1
    | ~ spl2_60 ),
    inference(avatar_split_clause,[],[f372,f367,f48,f68])).

fof(f68,plain,
    ( spl2_6
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f48,plain,
    ( spl2_1
  <=> k2_funct_1(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f367,plain,
    ( spl2_60
  <=> k2_funct_1(sK0) = k8_relat_1(k2_relat_1(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_60])])).

fof(f372,plain,
    ( k2_funct_1(sK0) = sK1
    | ~ v1_relat_1(sK1)
    | ~ spl2_60 ),
    inference(superposition,[],[f36,f368])).

fof(f368,plain,
    ( k2_funct_1(sK0) = k8_relat_1(k2_relat_1(sK1),sK1)
    | ~ spl2_60 ),
    inference(avatar_component_clause,[],[f367])).

fof(f36,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

fof(f370,plain,
    ( ~ spl2_6
    | spl2_60
    | ~ spl2_59 ),
    inference(avatar_split_clause,[],[f365,f361,f367,f68])).

fof(f361,plain,
    ( spl2_59
  <=> k2_funct_1(sK0) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).

fof(f365,plain,
    ( k2_funct_1(sK0) = k8_relat_1(k2_relat_1(sK1),sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl2_59 ),
    inference(superposition,[],[f46,f362])).

fof(f362,plain,
    ( k2_funct_1(sK0) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))
    | ~ spl2_59 ),
    inference(avatar_component_clause,[],[f361])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f363,plain,
    ( ~ spl2_8
    | ~ spl2_7
    | ~ spl2_4
    | spl2_59
    | ~ spl2_3
    | ~ spl2_57 ),
    inference(avatar_split_clause,[],[f359,f351,f56,f361,f60,f72,f76])).

fof(f76,plain,
    ( spl2_8
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f72,plain,
    ( spl2_7
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f60,plain,
    ( spl2_4
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f56,plain,
    ( spl2_3
  <=> k1_relat_1(sK0) = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f351,plain,
    ( spl2_57
  <=> k2_funct_1(sK0) = k5_relat_1(sK1,k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).

fof(f359,plain,
    ( k2_funct_1(sK0) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_3
    | ~ spl2_57 ),
    inference(forward_demodulation,[],[f358,f57])).

fof(f57,plain,
    ( k1_relat_1(sK0) = k2_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f358,plain,
    ( k2_funct_1(sK0) = k5_relat_1(sK1,k6_relat_1(k1_relat_1(sK0)))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_57 ),
    inference(superposition,[],[f352,f44])).

fof(f44,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f352,plain,
    ( k2_funct_1(sK0) = k5_relat_1(sK1,k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_57 ),
    inference(avatar_component_clause,[],[f351])).

fof(f353,plain,
    ( spl2_57
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_12
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f349,f278,f98,f76,f68,f52,f351])).

fof(f52,plain,
    ( spl2_2
  <=> k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f98,plain,
    ( spl2_12
  <=> k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f278,plain,
    ( spl2_45
  <=> ! [X3,X2] :
        ( ~ v1_relat_1(X2)
        | k5_relat_1(k5_relat_1(X3,X2),k2_funct_1(sK0)) = k5_relat_1(X3,k5_relat_1(X2,k2_funct_1(sK0)))
        | ~ v1_relat_1(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f349,plain,
    ( k2_funct_1(sK0) = k5_relat_1(sK1,k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_12
    | ~ spl2_45 ),
    inference(forward_demodulation,[],[f348,f99])).

fof(f99,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f98])).

fof(f348,plain,
    ( k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0)) = k5_relat_1(sK1,k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_45 ),
    inference(forward_demodulation,[],[f345,f53])).

fof(f53,plain,
    ( k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f345,plain,
    ( k5_relat_1(k5_relat_1(sK1,sK0),k2_funct_1(sK0)) = k5_relat_1(sK1,k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_45 ),
    inference(resolution,[],[f332,f69])).

fof(f69,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f332,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k5_relat_1(k5_relat_1(X1,sK0),k2_funct_1(sK0)) = k5_relat_1(X1,k5_relat_1(sK0,k2_funct_1(sK0))) )
    | ~ spl2_8
    | ~ spl2_45 ),
    inference(resolution,[],[f279,f77])).

fof(f77,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f76])).

fof(f279,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k5_relat_1(k5_relat_1(X3,X2),k2_funct_1(sK0)) = k5_relat_1(X3,k5_relat_1(X2,k2_funct_1(sK0)))
        | ~ v1_relat_1(X3) )
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f278])).

fof(f280,plain,
    ( ~ spl2_8
    | spl2_45
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f271,f72,f278,f76])).

fof(f271,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | ~ v1_relat_1(X3)
        | k5_relat_1(k5_relat_1(X3,X2),k2_funct_1(sK0)) = k5_relat_1(X3,k5_relat_1(X2,k2_funct_1(sK0)))
        | ~ v1_relat_1(sK0) )
    | ~ spl2_7 ),
    inference(resolution,[],[f121,f73])).

fof(f73,plain,
    ( v1_funct_1(sK0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f121,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_funct_1(X6)
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(X4)
      | k5_relat_1(k5_relat_1(X4,X5),k2_funct_1(X6)) = k5_relat_1(X4,k5_relat_1(X5,k2_funct_1(X6)))
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f38,f39])).

fof(f39,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f102,plain,
    ( ~ spl2_8
    | ~ spl2_7
    | spl2_11 ),
    inference(avatar_split_clause,[],[f101,f95,f72,f76])).

fof(f95,plain,
    ( spl2_11
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f101,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl2_11 ),
    inference(resolution,[],[f96,f39])).

fof(f96,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | spl2_11 ),
    inference(avatar_component_clause,[],[f95])).

fof(f100,plain,
    ( ~ spl2_11
    | spl2_12
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f93,f90,f98,f95])).

fof(f90,plain,
    ( spl2_10
  <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f93,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl2_10 ),
    inference(superposition,[],[f37,f91])).

fof(f91,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f90])).

fof(f37,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f92,plain,
    ( ~ spl2_8
    | ~ spl2_7
    | spl2_10
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f87,f60,f90,f72,f76])).

fof(f87,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f42,f61])).

fof(f61,plain,
    ( v2_funct_1(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f78,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f28,f76])).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k2_funct_1(sK0) != sK1
    & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)
    & k1_relat_1(sK0) = k2_relat_1(sK1)
    & v2_funct_1(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_funct_1(X0) != X1
            & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
            & k1_relat_1(X0) = k2_relat_1(X1)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_funct_1(sK0) != X1
          & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(X1,sK0)
          & k2_relat_1(X1) = k1_relat_1(sK0)
          & v2_funct_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( k2_funct_1(sK0) != X1
        & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(X1,sK0)
        & k2_relat_1(X1) = k1_relat_1(sK0)
        & v2_funct_1(sK0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_funct_1(sK0) != sK1
      & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)
      & k1_relat_1(sK0) = k2_relat_1(sK1)
      & v2_funct_1(sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
                & k1_relat_1(X0) = k2_relat_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f74,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f29,f72])).

fof(f29,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f30,f68])).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f32,f60])).

fof(f32,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f33,f56])).

fof(f33,plain,(
    k1_relat_1(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f54,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f34,f52])).

fof(f34,plain,(
    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f35,f48])).

fof(f35,plain,(
    k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:03:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (4029)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (4038)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (4030)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (4029)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (4037)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f376,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f50,f54,f58,f62,f70,f74,f78,f92,f100,f102,f280,f353,f363,f370,f375])).
% 0.21/0.48  fof(f375,plain,(
% 0.21/0.48    ~spl2_6 | spl2_1 | ~spl2_60),
% 0.21/0.48    inference(avatar_split_clause,[],[f372,f367,f48,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    spl2_6 <=> v1_relat_1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    spl2_1 <=> k2_funct_1(sK0) = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.48  fof(f367,plain,(
% 0.21/0.48    spl2_60 <=> k2_funct_1(sK0) = k8_relat_1(k2_relat_1(sK1),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_60])])).
% 0.21/0.48  fof(f372,plain,(
% 0.21/0.48    k2_funct_1(sK0) = sK1 | ~v1_relat_1(sK1) | ~spl2_60),
% 0.21/0.48    inference(superposition,[],[f36,f368])).
% 0.21/0.48  fof(f368,plain,(
% 0.21/0.48    k2_funct_1(sK0) = k8_relat_1(k2_relat_1(sK1),sK1) | ~spl2_60),
% 0.21/0.48    inference(avatar_component_clause,[],[f367])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).
% 0.21/0.48  fof(f370,plain,(
% 0.21/0.48    ~spl2_6 | spl2_60 | ~spl2_59),
% 0.21/0.48    inference(avatar_split_clause,[],[f365,f361,f367,f68])).
% 0.21/0.48  fof(f361,plain,(
% 0.21/0.48    spl2_59 <=> k2_funct_1(sK0) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).
% 0.21/0.48  fof(f365,plain,(
% 0.21/0.48    k2_funct_1(sK0) = k8_relat_1(k2_relat_1(sK1),sK1) | ~v1_relat_1(sK1) | ~spl2_59),
% 0.21/0.48    inference(superposition,[],[f46,f362])).
% 0.21/0.48  fof(f362,plain,(
% 0.21/0.48    k2_funct_1(sK0) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) | ~spl2_59),
% 0.21/0.48    inference(avatar_component_clause,[],[f361])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.21/0.48  fof(f363,plain,(
% 0.21/0.48    ~spl2_8 | ~spl2_7 | ~spl2_4 | spl2_59 | ~spl2_3 | ~spl2_57),
% 0.21/0.48    inference(avatar_split_clause,[],[f359,f351,f56,f361,f60,f72,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    spl2_8 <=> v1_relat_1(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    spl2_7 <=> v1_funct_1(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    spl2_4 <=> v2_funct_1(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    spl2_3 <=> k1_relat_1(sK0) = k2_relat_1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.48  fof(f351,plain,(
% 0.21/0.48    spl2_57 <=> k2_funct_1(sK0) = k5_relat_1(sK1,k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).
% 0.21/0.48  fof(f359,plain,(
% 0.21/0.48    k2_funct_1(sK0) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl2_3 | ~spl2_57)),
% 0.21/0.48    inference(forward_demodulation,[],[f358,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    k1_relat_1(sK0) = k2_relat_1(sK1) | ~spl2_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f56])).
% 0.21/0.48  fof(f358,plain,(
% 0.21/0.48    k2_funct_1(sK0) = k5_relat_1(sK1,k6_relat_1(k1_relat_1(sK0))) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl2_57),
% 0.21/0.48    inference(superposition,[],[f352,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.48  fof(f352,plain,(
% 0.21/0.48    k2_funct_1(sK0) = k5_relat_1(sK1,k5_relat_1(sK0,k2_funct_1(sK0))) | ~spl2_57),
% 0.21/0.48    inference(avatar_component_clause,[],[f351])).
% 0.21/0.48  fof(f353,plain,(
% 0.21/0.48    spl2_57 | ~spl2_2 | ~spl2_6 | ~spl2_8 | ~spl2_12 | ~spl2_45),
% 0.21/0.48    inference(avatar_split_clause,[],[f349,f278,f98,f76,f68,f52,f351])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    spl2_2 <=> k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    spl2_12 <=> k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.48  fof(f278,plain,(
% 0.21/0.48    spl2_45 <=> ! [X3,X2] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X3,X2),k2_funct_1(sK0)) = k5_relat_1(X3,k5_relat_1(X2,k2_funct_1(sK0))) | ~v1_relat_1(X3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 0.21/0.48  fof(f349,plain,(
% 0.21/0.48    k2_funct_1(sK0) = k5_relat_1(sK1,k5_relat_1(sK0,k2_funct_1(sK0))) | (~spl2_2 | ~spl2_6 | ~spl2_8 | ~spl2_12 | ~spl2_45)),
% 0.21/0.48    inference(forward_demodulation,[],[f348,f99])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0)) | ~spl2_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f98])).
% 0.21/0.48  fof(f348,plain,(
% 0.21/0.48    k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0)) = k5_relat_1(sK1,k5_relat_1(sK0,k2_funct_1(sK0))) | (~spl2_2 | ~spl2_6 | ~spl2_8 | ~spl2_45)),
% 0.21/0.48    inference(forward_demodulation,[],[f345,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) | ~spl2_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f52])).
% 0.21/0.48  fof(f345,plain,(
% 0.21/0.48    k5_relat_1(k5_relat_1(sK1,sK0),k2_funct_1(sK0)) = k5_relat_1(sK1,k5_relat_1(sK0,k2_funct_1(sK0))) | (~spl2_6 | ~spl2_8 | ~spl2_45)),
% 0.21/0.48    inference(resolution,[],[f332,f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    v1_relat_1(sK1) | ~spl2_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f68])).
% 0.21/0.48  fof(f332,plain,(
% 0.21/0.48    ( ! [X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(X1,sK0),k2_funct_1(sK0)) = k5_relat_1(X1,k5_relat_1(sK0,k2_funct_1(sK0)))) ) | (~spl2_8 | ~spl2_45)),
% 0.21/0.48    inference(resolution,[],[f279,f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    v1_relat_1(sK0) | ~spl2_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f76])).
% 0.21/0.48  fof(f279,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X3,X2),k2_funct_1(sK0)) = k5_relat_1(X3,k5_relat_1(X2,k2_funct_1(sK0))) | ~v1_relat_1(X3)) ) | ~spl2_45),
% 0.21/0.48    inference(avatar_component_clause,[],[f278])).
% 0.21/0.48  fof(f280,plain,(
% 0.21/0.48    ~spl2_8 | spl2_45 | ~spl2_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f271,f72,f278,f76])).
% 0.21/0.48  fof(f271,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~v1_relat_1(X2) | ~v1_relat_1(X3) | k5_relat_1(k5_relat_1(X3,X2),k2_funct_1(sK0)) = k5_relat_1(X3,k5_relat_1(X2,k2_funct_1(sK0))) | ~v1_relat_1(sK0)) ) | ~spl2_7),
% 0.21/0.48    inference(resolution,[],[f121,f73])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    v1_funct_1(sK0) | ~spl2_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f72])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    ( ! [X6,X4,X5] : (~v1_funct_1(X6) | ~v1_relat_1(X5) | ~v1_relat_1(X4) | k5_relat_1(k5_relat_1(X4,X5),k2_funct_1(X6)) = k5_relat_1(X4,k5_relat_1(X5,k2_funct_1(X6))) | ~v1_relat_1(X6)) )),
% 0.21/0.48    inference(resolution,[],[f38,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    ~spl2_8 | ~spl2_7 | spl2_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f101,f95,f72,f76])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    spl2_11 <=> v1_relat_1(k2_funct_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl2_11),
% 0.21/0.49    inference(resolution,[],[f96,f39])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ~v1_relat_1(k2_funct_1(sK0)) | spl2_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f95])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    ~spl2_11 | spl2_12 | ~spl2_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f93,f90,f98,f95])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    spl2_10 <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k2_funct_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0)) | ~spl2_10),
% 0.21/0.49    inference(superposition,[],[f37,f91])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~spl2_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f90])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    ~spl2_8 | ~spl2_7 | spl2_10 | ~spl2_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f87,f60,f90,f72,f76])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl2_4),
% 0.21/0.49    inference(resolution,[],[f42,f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    v2_funct_1(sK0) | ~spl2_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f60])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    spl2_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f28,f76])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    v1_relat_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    (k2_funct_1(sK0) != sK1 & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) & k1_relat_1(sK0) = k2_relat_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f26,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k2_funct_1(sK0) != X1 & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(X1,sK0) & k2_relat_1(X1) = k1_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ? [X1] : (k2_funct_1(sK0) != X1 & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(X1,sK0) & k2_relat_1(X1) = k1_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(sK0) != sK1 & k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) & k1_relat_1(sK0) = k2_relat_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.21/0.49    inference(negated_conjecture,[],[f9])).
% 0.21/0.49  fof(f9,conjecture,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    spl2_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f29,f72])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    v1_funct_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    spl2_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f30,f68])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    v1_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl2_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f32,f60])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    v2_funct_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    spl2_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f33,f56])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    k1_relat_1(sK0) = k2_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    spl2_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f34,f52])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ~spl2_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f35,f48])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    k2_funct_1(sK0) != sK1),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (4029)------------------------------
% 0.21/0.49  % (4029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (4029)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (4029)Memory used [KB]: 11001
% 0.21/0.49  % (4029)Time elapsed: 0.059 s
% 0.21/0.49  % (4029)------------------------------
% 0.21/0.49  % (4029)------------------------------
% 0.21/0.49  % (4018)Success in time 0.126 s
%------------------------------------------------------------------------------
