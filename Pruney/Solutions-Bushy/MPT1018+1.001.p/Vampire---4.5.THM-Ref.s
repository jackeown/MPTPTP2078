%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1018+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 108 expanded)
%              Number of leaves         :   13 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  217 ( 681 expanded)
%              Number of equality atoms :   49 ( 177 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f74,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f42,f47,f52,f57,f62,f67,f73])).

fof(f73,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f68,f36])).

fof(f36,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl6_2
  <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f68,plain,
    ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,sK3)
    | spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f66,f46,f31,f51,f41,f61,f56,f23])).

fof(f23,plain,(
    ! [X4,X0,X5,X1] :
      ( k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
      | X4 = X5
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_1(X1)
          | ( sK4(X0,X1) != sK5(X0,X1)
            & k1_funct_1(X1,sK4(X0,X1)) = k1_funct_1(X1,sK5(X0,X1))
            & r2_hidden(sK5(X0,X1),X0)
            & r2_hidden(sK4(X0,X1),X0) ) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X0) )
          | ~ v2_funct_1(X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f12,f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( sK4(X0,X1) != sK5(X0,X1)
        & k1_funct_1(X1,sK4(X0,X1)) = k1_funct_1(X1,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_1(X1)
          | ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) ) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X0) )
          | ~ v2_funct_1(X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(rectify,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_1(X1)
          | ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) ) )
        & ( ! [X2,X3] :
              ( X2 = X3
              | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          | ~ v2_funct_1(X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f56,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl6_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f61,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl6_7
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f41,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl6_3
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f51,plain,
    ( v2_funct_1(sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl6_5
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f31,plain,
    ( sK2 != sK3
    | spl6_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl6_1
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f46,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl6_4
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f66,plain,
    ( v1_funct_1(sK1)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl6_8
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f67,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f15,f64])).

fof(f15,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( sK2 != sK3
    & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    & r2_hidden(sK3,sK0)
    & r2_hidden(sK2,sK0)
    & v2_funct_1(sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f9,f8])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        & v2_funct_1(X1)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X3,X2] :
          ( X2 != X3
          & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
          & r2_hidden(X3,sK0)
          & r2_hidden(X2,sK0) )
      & v2_funct_1(sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,
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

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_2)).

fof(f62,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f16,f59])).

fof(f16,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f57,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f17,f54])).

fof(f17,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f52,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f18,f49])).

fof(f18,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f47,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f19,f44])).

fof(f19,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f20,f39])).

fof(f20,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f37,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f21,f34])).

fof(f21,plain,(
    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f32,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f22,f29])).

fof(f22,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f10])).

%------------------------------------------------------------------------------
