%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1084+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 200 expanded)
%              Number of leaves         :   24 (  86 expanded)
%              Depth                    :    9
%              Number of atoms          :  321 ( 828 expanded)
%              Number of equality atoms :   47 ( 117 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f164,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f65,f70,f75,f94,f119,f124,f160,f161,f162,f163])).

fof(f163,plain,
    ( k1_funct_1(sK1,sK2(sK0,sK1,k6_relat_1(sK0))) != k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1,k6_relat_1(sK0)))
    | sK2(sK0,sK1,k6_relat_1(sK0)) != k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1,k6_relat_1(sK0)))
    | sK2(sK0,sK1,k6_relat_1(sK0)) != k1_funct_1(k6_relat_1(sK0),sK2(sK0,sK1,k6_relat_1(sK0)))
    | k1_funct_1(sK1,sK2(sK0,sK1,k6_relat_1(sK0))) = k1_funct_1(k6_relat_1(sK0),sK2(sK0,sK1,k6_relat_1(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f162,plain,
    ( spl3_14
    | spl3_5
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f133,f121,f72,f140])).

fof(f140,plain,
    ( spl3_14
  <=> sK2(sK0,sK1,k6_relat_1(sK0)) = k1_funct_1(k6_relat_1(sK0),sK2(sK0,sK1,k6_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f72,plain,
    ( spl3_5
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f121,plain,
    ( spl3_12
  <=> m1_subset_1(sK2(sK0,sK1,k6_relat_1(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f133,plain,
    ( v1_xboole_0(sK0)
    | sK2(sK0,sK1,k6_relat_1(sK0)) = k1_funct_1(k6_relat_1(sK0),sK2(sK0,sK1,k6_relat_1(sK0)))
    | ~ spl3_12 ),
    inference(resolution,[],[f123,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k1_funct_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(resolution,[],[f40,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).

fof(f123,plain,
    ( m1_subset_1(sK2(sK0,sK1,k6_relat_1(sK0)),sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f121])).

fof(f161,plain,
    ( spl3_17
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f132,f121,f155])).

fof(f155,plain,
    ( spl3_17
  <=> sK2(sK0,sK1,k6_relat_1(sK0)) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1,k6_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f132,plain,
    ( sK2(sK0,sK1,k6_relat_1(sK0)) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1,k6_relat_1(sK0)))
    | ~ spl3_12 ),
    inference(resolution,[],[f123,f33])).

fof(f33,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | k3_funct_2(sK0,sK0,sK1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))
    & ! [X2] :
        ( k3_funct_2(sK0,sK0,sK1,X2) = X2
        | ~ m1_subset_1(X2,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
            & ! [X2] :
                ( k3_funct_2(X0,X0,X1,X2) = X2
                | ~ m1_subset_1(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ~ r2_funct_2(sK0,sK0,X1,k6_partfun1(sK0))
          & ! [X2] :
              ( k3_funct_2(sK0,sK0,X1,X2) = X2
              | ~ m1_subset_1(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_2(X1,sK0,sK0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ~ r2_funct_2(sK0,sK0,X1,k6_partfun1(sK0))
        & ! [X2] :
            ( k3_funct_2(sK0,sK0,X1,X2) = X2
            | ~ m1_subset_1(X2,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v1_funct_2(X1,sK0,sK0)
        & v1_funct_1(X1) )
   => ( ~ r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))
      & ! [X2] :
          ( k3_funct_2(sK0,sK0,sK1,X2) = X2
          | ~ m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
          & ! [X2] :
              ( k3_funct_2(X0,X0,X1,X2) = X2
              | ~ m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
          & ! [X2] :
              ( k3_funct_2(X0,X0,X1,X2) = X2
              | ~ m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X1,X0,X0)
              & v1_funct_1(X1) )
           => ( ! [X2] :
                  ( m1_subset_1(X2,X0)
                 => k3_funct_2(X0,X0,X1,X2) = X2 )
             => r2_funct_2(X0,X0,X1,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,X0)
               => k3_funct_2(X0,X0,X1,X2) = X2 )
           => r2_funct_2(X0,X0,X1,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t201_funct_2)).

fof(f160,plain,
    ( spl3_16
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f131,f121,f92,f150])).

fof(f150,plain,
    ( spl3_16
  <=> k1_funct_1(sK1,sK2(sK0,sK1,k6_relat_1(sK0))) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1,k6_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f92,plain,
    ( spl3_8
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f131,plain,
    ( k1_funct_1(sK1,sK2(sK0,sK1,k6_relat_1(sK0))) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1,k6_relat_1(sK0)))
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(resolution,[],[f123,f93])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f92])).

fof(f124,plain,
    ( spl3_12
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f111,f67,f62,f57,f52,f121])).

fof(f52,plain,
    ( spl3_1
  <=> r2_funct_2(sK0,sK0,sK1,k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f57,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f62,plain,
    ( spl3_3
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f67,plain,
    ( spl3_4
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f111,plain,
    ( m1_subset_1(sK2(sK0,sK1,k6_relat_1(sK0)),sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f69,f37,f64,f54,f59,f49,f88,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | m1_subset_1(sK2(X0,X2,X3),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ( k1_funct_1(X2,sK2(X0,X2,X3)) != k1_funct_1(X3,sK2(X0,X2,X3))
                & m1_subset_1(sK2(X0,X2,X3),X0) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ m1_subset_1(X5,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).

fof(f27,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & m1_subset_1(X4,X0) )
     => ( k1_funct_1(X2,sK2(X0,X2,X3)) != k1_funct_1(X3,sK2(X0,X2,X3))
        & m1_subset_1(sK2(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ m1_subset_1(X5,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X4] :
                  ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                  | ~ m1_subset_1(X4,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_2)).

fof(f88,plain,(
    ! [X0] : v1_funct_2(k6_relat_1(X0),X0,X0) ),
    inference(unit_resulting_resolution,[],[f37,f50,f49,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f50,plain,(
    ! [X0] : v1_partfun1(k6_relat_1(X0),X0) ),
    inference(definition_unfolding,[],[f38,f35])).

fof(f35,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f38,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f39,f35])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f3])).

fof(f59,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f54,plain,
    ( ~ r2_funct_2(sK0,sK0,sK1,k6_relat_1(sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f64,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f37,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f69,plain,
    ( v1_funct_1(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f119,plain,
    ( ~ spl3_11
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f112,f67,f62,f57,f52,f116])).

fof(f116,plain,
    ( spl3_11
  <=> k1_funct_1(sK1,sK2(sK0,sK1,k6_relat_1(sK0))) = k1_funct_1(k6_relat_1(sK0),sK2(sK0,sK1,k6_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f112,plain,
    ( k1_funct_1(sK1,sK2(sK0,sK1,k6_relat_1(sK0))) != k1_funct_1(k6_relat_1(sK0),sK2(sK0,sK1,k6_relat_1(sK0)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f69,f37,f64,f59,f54,f49,f88,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,sK2(X0,X2,X3)) != k1_funct_1(X3,sK2(X0,X2,X3))
      | r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f94,plain,
    ( spl3_5
    | ~ spl3_4
    | ~ spl3_2
    | spl3_8
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f90,f62,f92,f57,f67,f72])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0)
        | ~ v1_funct_1(sK1)
        | v1_xboole_0(sK0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f47,f64])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f75,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f29,f72])).

fof(f29,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f30,f67])).

fof(f30,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f31,f62])).

fof(f31,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f32,f57])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f48,f52])).

fof(f48,plain,(
    ~ r2_funct_2(sK0,sK0,sK1,k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f34,plain,(
    ~ r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

%------------------------------------------------------------------------------
