%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 215 expanded)
%              Number of leaves         :   36 (  93 expanded)
%              Depth                    :   10
%              Number of atoms          :  436 ( 798 expanded)
%              Number of equality atoms :   97 ( 167 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f315,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f78,f82,f86,f97,f107,f116,f119,f127,f137,f142,f183,f190,f204,f209,f266,f297,f304,f305,f313,f314])).

fof(f314,plain,
    ( sK1 != k1_relat_1(sK3)
    | r2_hidden(sK6(sK3,sK0),sK1)
    | ~ r2_hidden(sK6(sK3,sK0),k1_relat_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f313,plain,
    ( ~ spl7_2
    | spl7_40
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f307,f260,f310,f76])).

fof(f76,plain,
    ( spl7_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f310,plain,
    ( spl7_40
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f260,plain,
    ( spl7_31
  <=> sK1 = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f307,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_31 ),
    inference(superposition,[],[f53,f261])).

fof(f261,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f260])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f305,plain,
    ( ~ spl7_39
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f302,f295,f299])).

fof(f299,plain,
    ( spl7_39
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f295,plain,
    ( spl7_38
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f302,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ spl7_38 ),
    inference(resolution,[],[f296,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f296,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f295])).

fof(f304,plain,(
    spl7_39 ),
    inference(avatar_contradiction_clause,[],[f303])).

fof(f303,plain,
    ( $false
    | spl7_39 ),
    inference(resolution,[],[f300,f42])).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f300,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl7_39 ),
    inference(avatar_component_clause,[],[f299])).

fof(f297,plain,
    ( spl7_38
    | ~ spl7_11
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f275,f263,f125,f295])).

fof(f125,plain,
    ( spl7_11
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f263,plain,
    ( spl7_32
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f275,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl7_11
    | ~ spl7_32 ),
    inference(superposition,[],[f126,f264])).

fof(f264,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f263])).

fof(f126,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f125])).

fof(f266,plain,
    ( spl7_31
    | spl7_32
    | ~ spl7_3
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f258,f76,f80,f263,f260])).

fof(f80,plain,
    ( spl7_3
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f258,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl7_2 ),
    inference(resolution,[],[f56,f77])).

fof(f77,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f209,plain,
    ( ~ spl7_26
    | spl7_25 ),
    inference(avatar_split_clause,[],[f205,f202,f207])).

fof(f207,plain,
    ( spl7_26
  <=> r2_hidden(sK6(sK3,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f202,plain,
    ( spl7_25
  <=> m1_subset_1(sK6(sK3,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f205,plain,
    ( ~ r2_hidden(sK6(sK3,sK0),sK1)
    | spl7_25 ),
    inference(resolution,[],[f203,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f203,plain,
    ( ~ m1_subset_1(sK6(sK3,sK0),sK1)
    | spl7_25 ),
    inference(avatar_component_clause,[],[f202])).

fof(f204,plain,
    ( ~ spl7_25
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f200,f188,f202])).

fof(f188,plain,
    ( spl7_23
  <=> sK0 = k1_funct_1(sK3,sK6(sK3,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f200,plain,
    ( ~ m1_subset_1(sK6(sK3,sK0),sK1)
    | ~ spl7_23 ),
    inference(trivial_inequality_removal,[],[f199])).

fof(f199,plain,
    ( sK0 != sK0
    | ~ m1_subset_1(sK6(sK3,sK0),sK1)
    | ~ spl7_23 ),
    inference(superposition,[],[f41,f189])).

fof(f189,plain,
    ( sK0 = k1_funct_1(sK3,sK6(sK3,sK0))
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f188])).

fof(f41,plain,(
    ! [X4] :
      ( sK0 != k1_funct_1(sK3,X4)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ! [X4] :
        ( sK0 != k1_funct_1(sK3,X4)
        | ~ m1_subset_1(X4,sK1) )
    & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X0
            | ~ m1_subset_1(X4,X1) )
        & r2_hidden(X0,k2_relset_1(X1,X2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( sK0 != k1_funct_1(sK3,X4)
          | ~ m1_subset_1(X4,sK1) )
      & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

fof(f190,plain,
    ( spl7_23
    | ~ spl7_8
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f185,f181,f105,f188])).

fof(f105,plain,
    ( spl7_8
  <=> r2_hidden(sK0,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f181,plain,
    ( spl7_22
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | k1_funct_1(sK3,sK6(sK3,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f185,plain,
    ( sK0 = k1_funct_1(sK3,sK6(sK3,sK0))
    | ~ spl7_8
    | ~ spl7_22 ),
    inference(resolution,[],[f182,f106])).

fof(f106,plain,
    ( r2_hidden(sK0,k2_relat_1(sK3))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | k1_funct_1(sK3,sK6(sK3,X0)) = X0 )
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f181])).

fof(f183,plain,
    ( ~ spl7_9
    | spl7_22
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f179,f84,f181,f111])).

fof(f111,plain,
    ( spl7_9
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f84,plain,
    ( spl7_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f179,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | k1_funct_1(sK3,sK6(sK3,X0)) = X0
        | ~ v1_relat_1(sK3) )
    | ~ spl7_4 ),
    inference(resolution,[],[f64,f85])).

fof(f85,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f64,plain,(
    ! [X0,X5] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f31,f34,f33,f32])).

fof(f32,plain,(
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

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK4(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

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

fof(f142,plain,
    ( spl7_14
    | ~ spl7_8
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f138,f135,f105,f140])).

fof(f140,plain,
    ( spl7_14
  <=> r2_hidden(sK6(sK3,sK0),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f135,plain,
    ( spl7_13
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | r2_hidden(sK6(sK3,X0),k1_relat_1(sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f138,plain,
    ( r2_hidden(sK6(sK3,sK0),k1_relat_1(sK3))
    | ~ spl7_8
    | ~ spl7_13 ),
    inference(resolution,[],[f136,f106])).

fof(f136,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | r2_hidden(sK6(sK3,X0),k1_relat_1(sK3)) )
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f135])).

fof(f137,plain,
    ( ~ spl7_9
    | spl7_13
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f133,f84,f135,f111])).

fof(f133,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | r2_hidden(sK6(sK3,X0),k1_relat_1(sK3))
        | ~ v1_relat_1(sK3) )
    | ~ spl7_4 ),
    inference(resolution,[],[f65,f85])).

% (31966)Refutation not found, incomplete strategy% (31966)------------------------------
% (31966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f65,plain,(
    ! [X0,X5] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f43])).

% (31966)Termination reason: Refutation not found, incomplete strategy

% (31966)Memory used [KB]: 10618
% (31966)Time elapsed: 0.102 s
fof(f43,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

% (31966)------------------------------
% (31966)------------------------------
fof(f127,plain,
    ( spl7_11
    | ~ spl7_2
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f122,f114,f76,f125])).

fof(f114,plain,
    ( spl7_10
  <=> ! [X0] :
        ( r2_hidden(sK0,X0)
        | ~ v5_relat_1(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f122,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl7_2
    | ~ spl7_10 ),
    inference(resolution,[],[f121,f77])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | r2_hidden(sK0,X0) )
    | ~ spl7_10 ),
    inference(resolution,[],[f115,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f115,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(sK3,X0)
        | r2_hidden(sK0,X0) )
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f119,plain,
    ( ~ spl7_2
    | spl7_9 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | ~ spl7_2
    | spl7_9 ),
    inference(subsumption_resolution,[],[f77,f117])).

fof(f117,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl7_9 ),
    inference(resolution,[],[f112,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f112,plain,
    ( ~ v1_relat_1(sK3)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f111])).

fof(f116,plain,
    ( ~ spl7_9
    | spl7_10
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f108,f105,f114,f111])).

fof(f108,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,X0)
        | ~ v5_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3) )
    | ~ spl7_8 ),
    inference(resolution,[],[f106,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_relat_1(X1))
      | r2_hidden(X2,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k2_relat_1(X1))
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).

fof(f107,plain,
    ( spl7_8
    | ~ spl7_1
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f99,f95,f72,f105])).

fof(f72,plain,
    ( spl7_1
  <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f95,plain,
    ( spl7_6
  <=> k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f99,plain,
    ( r2_hidden(sK0,k2_relat_1(sK3))
    | ~ spl7_1
    | ~ spl7_6 ),
    inference(superposition,[],[f73,f96])).

fof(f96,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f73,plain,
    ( r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f97,plain,
    ( spl7_6
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f92,f76,f95])).

fof(f92,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl7_2 ),
    inference(resolution,[],[f54,f77])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f86,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f37,f84])).

fof(f37,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f82,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f38,f80])).

fof(f38,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f39,f76])).

fof(f39,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f40,f72])).

fof(f40,plain,(
    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:01:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (31962)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  % (31952)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (31960)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (31951)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (31952)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (31954)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.51  % (31946)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (31959)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.51  % (31947)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (31965)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.51  % (31953)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.52  % (31961)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.52  % (31957)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.52  % (31950)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.52  % (31955)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.52  % (31966)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.52  % (31958)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.26/0.52  % SZS output start Proof for theBenchmark
% 1.26/0.52  fof(f315,plain,(
% 1.26/0.52    $false),
% 1.26/0.52    inference(avatar_sat_refutation,[],[f74,f78,f82,f86,f97,f107,f116,f119,f127,f137,f142,f183,f190,f204,f209,f266,f297,f304,f305,f313,f314])).
% 1.26/0.52  fof(f314,plain,(
% 1.26/0.52    sK1 != k1_relat_1(sK3) | r2_hidden(sK6(sK3,sK0),sK1) | ~r2_hidden(sK6(sK3,sK0),k1_relat_1(sK3))),
% 1.26/0.52    introduced(theory_tautology_sat_conflict,[])).
% 1.26/0.52  fof(f313,plain,(
% 1.26/0.52    ~spl7_2 | spl7_40 | ~spl7_31),
% 1.26/0.52    inference(avatar_split_clause,[],[f307,f260,f310,f76])).
% 1.26/0.52  fof(f76,plain,(
% 1.26/0.52    spl7_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.26/0.52  fof(f310,plain,(
% 1.26/0.52    spl7_40 <=> sK1 = k1_relat_1(sK3)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).
% 1.26/0.52  fof(f260,plain,(
% 1.26/0.52    spl7_31 <=> sK1 = k1_relset_1(sK1,sK2,sK3)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 1.26/0.52  fof(f307,plain,(
% 1.26/0.52    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl7_31),
% 1.26/0.52    inference(superposition,[],[f53,f261])).
% 1.26/0.52  fof(f261,plain,(
% 1.26/0.52    sK1 = k1_relset_1(sK1,sK2,sK3) | ~spl7_31),
% 1.26/0.52    inference(avatar_component_clause,[],[f260])).
% 1.26/0.52  fof(f53,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.26/0.52    inference(cnf_transformation,[],[f23])).
% 1.26/0.52  fof(f23,plain,(
% 1.26/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.26/0.52    inference(ennf_transformation,[],[f8])).
% 1.26/0.52  fof(f8,axiom,(
% 1.26/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.26/0.52  fof(f305,plain,(
% 1.26/0.52    ~spl7_39 | ~spl7_38),
% 1.26/0.52    inference(avatar_split_clause,[],[f302,f295,f299])).
% 1.26/0.52  fof(f299,plain,(
% 1.26/0.52    spl7_39 <=> r1_tarski(k1_xboole_0,sK0)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 1.26/0.52  fof(f295,plain,(
% 1.26/0.52    spl7_38 <=> r2_hidden(sK0,k1_xboole_0)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).
% 1.26/0.52  fof(f302,plain,(
% 1.26/0.52    ~r1_tarski(k1_xboole_0,sK0) | ~spl7_38),
% 1.26/0.52    inference(resolution,[],[f296,f51])).
% 1.26/0.52  fof(f51,plain,(
% 1.26/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f21])).
% 1.26/0.52  fof(f21,plain,(
% 1.26/0.52    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.26/0.52    inference(ennf_transformation,[],[f5])).
% 1.26/0.52  fof(f5,axiom,(
% 1.26/0.52    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.26/0.52  fof(f296,plain,(
% 1.26/0.52    r2_hidden(sK0,k1_xboole_0) | ~spl7_38),
% 1.26/0.52    inference(avatar_component_clause,[],[f295])).
% 1.26/0.52  fof(f304,plain,(
% 1.26/0.52    spl7_39),
% 1.26/0.52    inference(avatar_contradiction_clause,[],[f303])).
% 1.26/0.52  fof(f303,plain,(
% 1.26/0.52    $false | spl7_39),
% 1.26/0.52    inference(resolution,[],[f300,f42])).
% 1.26/0.52  fof(f42,plain,(
% 1.26/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f1])).
% 1.26/0.52  fof(f1,axiom,(
% 1.26/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.26/0.52  fof(f300,plain,(
% 1.26/0.52    ~r1_tarski(k1_xboole_0,sK0) | spl7_39),
% 1.26/0.52    inference(avatar_component_clause,[],[f299])).
% 1.26/0.52  fof(f297,plain,(
% 1.26/0.52    spl7_38 | ~spl7_11 | ~spl7_32),
% 1.26/0.52    inference(avatar_split_clause,[],[f275,f263,f125,f295])).
% 1.26/0.52  fof(f125,plain,(
% 1.26/0.52    spl7_11 <=> r2_hidden(sK0,sK2)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.26/0.52  fof(f263,plain,(
% 1.26/0.52    spl7_32 <=> k1_xboole_0 = sK2),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 1.26/0.52  fof(f275,plain,(
% 1.26/0.52    r2_hidden(sK0,k1_xboole_0) | (~spl7_11 | ~spl7_32)),
% 1.26/0.52    inference(superposition,[],[f126,f264])).
% 1.26/0.52  fof(f264,plain,(
% 1.26/0.52    k1_xboole_0 = sK2 | ~spl7_32),
% 1.26/0.52    inference(avatar_component_clause,[],[f263])).
% 1.26/0.52  fof(f126,plain,(
% 1.26/0.52    r2_hidden(sK0,sK2) | ~spl7_11),
% 1.26/0.52    inference(avatar_component_clause,[],[f125])).
% 1.26/0.52  fof(f266,plain,(
% 1.26/0.52    spl7_31 | spl7_32 | ~spl7_3 | ~spl7_2),
% 1.26/0.52    inference(avatar_split_clause,[],[f258,f76,f80,f263,f260])).
% 1.26/0.52  fof(f80,plain,(
% 1.26/0.52    spl7_3 <=> v1_funct_2(sK3,sK1,sK2)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.26/0.52  fof(f258,plain,(
% 1.26/0.52    ~v1_funct_2(sK3,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | ~spl7_2),
% 1.26/0.52    inference(resolution,[],[f56,f77])).
% 1.26/0.52  fof(f77,plain,(
% 1.26/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl7_2),
% 1.26/0.52    inference(avatar_component_clause,[],[f76])).
% 1.26/0.52  fof(f56,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.26/0.52    inference(cnf_transformation,[],[f36])).
% 1.26/0.52  fof(f36,plain,(
% 1.26/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.26/0.52    inference(nnf_transformation,[],[f27])).
% 1.26/0.52  fof(f27,plain,(
% 1.26/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.26/0.52    inference(flattening,[],[f26])).
% 1.26/0.52  fof(f26,plain,(
% 1.26/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.26/0.52    inference(ennf_transformation,[],[f10])).
% 1.26/0.52  fof(f10,axiom,(
% 1.26/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.26/0.52  fof(f209,plain,(
% 1.26/0.52    ~spl7_26 | spl7_25),
% 1.26/0.52    inference(avatar_split_clause,[],[f205,f202,f207])).
% 1.26/0.52  fof(f207,plain,(
% 1.26/0.52    spl7_26 <=> r2_hidden(sK6(sK3,sK0),sK1)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 1.26/0.52  fof(f202,plain,(
% 1.26/0.52    spl7_25 <=> m1_subset_1(sK6(sK3,sK0),sK1)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 1.26/0.52  fof(f205,plain,(
% 1.26/0.52    ~r2_hidden(sK6(sK3,sK0),sK1) | spl7_25),
% 1.26/0.52    inference(resolution,[],[f203,f49])).
% 1.26/0.52  fof(f49,plain,(
% 1.26/0.52    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f18])).
% 1.26/0.52  fof(f18,plain,(
% 1.26/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.26/0.52    inference(ennf_transformation,[],[f2])).
% 1.26/0.52  fof(f2,axiom,(
% 1.26/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.26/0.52  fof(f203,plain,(
% 1.26/0.52    ~m1_subset_1(sK6(sK3,sK0),sK1) | spl7_25),
% 1.26/0.52    inference(avatar_component_clause,[],[f202])).
% 1.26/0.52  fof(f204,plain,(
% 1.26/0.52    ~spl7_25 | ~spl7_23),
% 1.26/0.52    inference(avatar_split_clause,[],[f200,f188,f202])).
% 1.26/0.52  fof(f188,plain,(
% 1.26/0.52    spl7_23 <=> sK0 = k1_funct_1(sK3,sK6(sK3,sK0))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 1.26/0.52  fof(f200,plain,(
% 1.26/0.52    ~m1_subset_1(sK6(sK3,sK0),sK1) | ~spl7_23),
% 1.26/0.52    inference(trivial_inequality_removal,[],[f199])).
% 1.26/0.52  fof(f199,plain,(
% 1.26/0.52    sK0 != sK0 | ~m1_subset_1(sK6(sK3,sK0),sK1) | ~spl7_23),
% 1.26/0.52    inference(superposition,[],[f41,f189])).
% 1.26/0.52  fof(f189,plain,(
% 1.26/0.52    sK0 = k1_funct_1(sK3,sK6(sK3,sK0)) | ~spl7_23),
% 1.26/0.52    inference(avatar_component_clause,[],[f188])).
% 1.26/0.52  fof(f41,plain,(
% 1.26/0.52    ( ! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f29])).
% 1.26/0.52  fof(f29,plain,(
% 1.26/0.52    ! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 1.26/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f28])).
% 1.26/0.52  fof(f28,plain,(
% 1.26/0.52    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 1.26/0.52    introduced(choice_axiom,[])).
% 1.26/0.52  fof(f15,plain,(
% 1.26/0.52    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))),
% 1.26/0.52    inference(flattening,[],[f14])).
% 1.26/0.52  fof(f14,plain,(
% 1.26/0.52    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)))),
% 1.26/0.52    inference(ennf_transformation,[],[f12])).
% 1.26/0.52  fof(f12,negated_conjecture,(
% 1.26/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 1.26/0.52    inference(negated_conjecture,[],[f11])).
% 1.26/0.52  fof(f11,conjecture,(
% 1.26/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).
% 1.26/0.52  fof(f190,plain,(
% 1.26/0.52    spl7_23 | ~spl7_8 | ~spl7_22),
% 1.26/0.52    inference(avatar_split_clause,[],[f185,f181,f105,f188])).
% 1.26/0.52  fof(f105,plain,(
% 1.26/0.52    spl7_8 <=> r2_hidden(sK0,k2_relat_1(sK3))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.26/0.52  fof(f181,plain,(
% 1.26/0.52    spl7_22 <=> ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | k1_funct_1(sK3,sK6(sK3,X0)) = X0)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 1.26/0.52  fof(f185,plain,(
% 1.26/0.52    sK0 = k1_funct_1(sK3,sK6(sK3,sK0)) | (~spl7_8 | ~spl7_22)),
% 1.26/0.52    inference(resolution,[],[f182,f106])).
% 1.26/0.52  fof(f106,plain,(
% 1.26/0.52    r2_hidden(sK0,k2_relat_1(sK3)) | ~spl7_8),
% 1.26/0.52    inference(avatar_component_clause,[],[f105])).
% 1.26/0.52  fof(f182,plain,(
% 1.26/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | k1_funct_1(sK3,sK6(sK3,X0)) = X0) ) | ~spl7_22),
% 1.26/0.52    inference(avatar_component_clause,[],[f181])).
% 1.26/0.52  fof(f183,plain,(
% 1.26/0.52    ~spl7_9 | spl7_22 | ~spl7_4),
% 1.26/0.52    inference(avatar_split_clause,[],[f179,f84,f181,f111])).
% 1.26/0.52  fof(f111,plain,(
% 1.26/0.52    spl7_9 <=> v1_relat_1(sK3)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.26/0.52  fof(f84,plain,(
% 1.26/0.52    spl7_4 <=> v1_funct_1(sK3)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.26/0.52  fof(f179,plain,(
% 1.26/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | k1_funct_1(sK3,sK6(sK3,X0)) = X0 | ~v1_relat_1(sK3)) ) | ~spl7_4),
% 1.26/0.52    inference(resolution,[],[f64,f85])).
% 1.26/0.52  fof(f85,plain,(
% 1.26/0.52    v1_funct_1(sK3) | ~spl7_4),
% 1.26/0.52    inference(avatar_component_clause,[],[f84])).
% 1.26/0.52  fof(f64,plain,(
% 1.26/0.52    ( ! [X0,X5] : (~v1_funct_1(X0) | ~r2_hidden(X5,k2_relat_1(X0)) | k1_funct_1(X0,sK6(X0,X5)) = X5 | ~v1_relat_1(X0)) )),
% 1.26/0.52    inference(equality_resolution,[],[f44])).
% 1.26/0.52  fof(f44,plain,(
% 1.26/0.52    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK6(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f35])).
% 1.26/0.52  fof(f35,plain,(
% 1.26/0.52    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & ((sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.26/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f31,f34,f33,f32])).
% 1.26/0.52  fof(f32,plain,(
% 1.26/0.52    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1))))),
% 1.26/0.52    introduced(choice_axiom,[])).
% 1.26/0.52  fof(f33,plain,(
% 1.26/0.52    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 1.26/0.52    introduced(choice_axiom,[])).
% 1.26/0.52  fof(f34,plain,(
% 1.26/0.52    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))))),
% 1.26/0.52    introduced(choice_axiom,[])).
% 1.26/0.52  fof(f31,plain,(
% 1.26/0.52    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.26/0.52    inference(rectify,[],[f30])).
% 1.26/0.52  fof(f30,plain,(
% 1.26/0.52    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.26/0.52    inference(nnf_transformation,[],[f17])).
% 1.26/0.52  fof(f17,plain,(
% 1.26/0.52    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.26/0.52    inference(flattening,[],[f16])).
% 1.26/0.52  fof(f16,plain,(
% 1.26/0.52    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.26/0.52    inference(ennf_transformation,[],[f4])).
% 1.26/0.52  fof(f4,axiom,(
% 1.26/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 1.26/0.52  fof(f142,plain,(
% 1.26/0.52    spl7_14 | ~spl7_8 | ~spl7_13),
% 1.26/0.52    inference(avatar_split_clause,[],[f138,f135,f105,f140])).
% 1.26/0.52  fof(f140,plain,(
% 1.26/0.52    spl7_14 <=> r2_hidden(sK6(sK3,sK0),k1_relat_1(sK3))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 1.26/0.52  fof(f135,plain,(
% 1.26/0.52    spl7_13 <=> ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(sK6(sK3,X0),k1_relat_1(sK3)))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.26/0.52  fof(f138,plain,(
% 1.26/0.52    r2_hidden(sK6(sK3,sK0),k1_relat_1(sK3)) | (~spl7_8 | ~spl7_13)),
% 1.26/0.52    inference(resolution,[],[f136,f106])).
% 1.26/0.52  fof(f136,plain,(
% 1.26/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(sK6(sK3,X0),k1_relat_1(sK3))) ) | ~spl7_13),
% 1.26/0.52    inference(avatar_component_clause,[],[f135])).
% 1.26/0.52  fof(f137,plain,(
% 1.26/0.52    ~spl7_9 | spl7_13 | ~spl7_4),
% 1.26/0.52    inference(avatar_split_clause,[],[f133,f84,f135,f111])).
% 1.26/0.52  fof(f133,plain,(
% 1.26/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(sK6(sK3,X0),k1_relat_1(sK3)) | ~v1_relat_1(sK3)) ) | ~spl7_4),
% 1.26/0.52    inference(resolution,[],[f65,f85])).
% 1.26/0.52  % (31966)Refutation not found, incomplete strategy% (31966)------------------------------
% 1.26/0.52  % (31966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.52  fof(f65,plain,(
% 1.26/0.52    ( ! [X0,X5] : (~v1_funct_1(X0) | ~r2_hidden(X5,k2_relat_1(X0)) | r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.26/0.52    inference(equality_resolution,[],[f43])).
% 1.26/0.52  % (31966)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.52  
% 1.26/0.52  % (31966)Memory used [KB]: 10618
% 1.26/0.52  % (31966)Time elapsed: 0.102 s
% 1.26/0.52  fof(f43,plain,(
% 1.26/0.52    ( ! [X0,X5,X1] : (r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f35])).
% 1.26/0.52  % (31966)------------------------------
% 1.26/0.52  % (31966)------------------------------
% 1.26/0.52  fof(f127,plain,(
% 1.26/0.52    spl7_11 | ~spl7_2 | ~spl7_10),
% 1.26/0.52    inference(avatar_split_clause,[],[f122,f114,f76,f125])).
% 1.26/0.52  fof(f114,plain,(
% 1.26/0.52    spl7_10 <=> ! [X0] : (r2_hidden(sK0,X0) | ~v5_relat_1(sK3,X0))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.26/0.52  fof(f122,plain,(
% 1.26/0.52    r2_hidden(sK0,sK2) | (~spl7_2 | ~spl7_10)),
% 1.26/0.52    inference(resolution,[],[f121,f77])).
% 1.26/0.52  fof(f121,plain,(
% 1.26/0.52    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | r2_hidden(sK0,X0)) ) | ~spl7_10),
% 1.26/0.52    inference(resolution,[],[f115,f55])).
% 1.26/0.52  fof(f55,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.26/0.52    inference(cnf_transformation,[],[f25])).
% 1.26/0.52  fof(f25,plain,(
% 1.26/0.52    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.26/0.52    inference(ennf_transformation,[],[f13])).
% 1.26/0.52  fof(f13,plain,(
% 1.26/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.26/0.52    inference(pure_predicate_removal,[],[f7])).
% 1.26/0.52  fof(f7,axiom,(
% 1.26/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.26/0.52  fof(f115,plain,(
% 1.26/0.52    ( ! [X0] : (~v5_relat_1(sK3,X0) | r2_hidden(sK0,X0)) ) | ~spl7_10),
% 1.26/0.52    inference(avatar_component_clause,[],[f114])).
% 1.26/0.52  fof(f119,plain,(
% 1.26/0.52    ~spl7_2 | spl7_9),
% 1.26/0.52    inference(avatar_contradiction_clause,[],[f118])).
% 1.26/0.52  fof(f118,plain,(
% 1.26/0.52    $false | (~spl7_2 | spl7_9)),
% 1.26/0.52    inference(subsumption_resolution,[],[f77,f117])).
% 1.26/0.52  fof(f117,plain,(
% 1.26/0.52    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl7_9),
% 1.26/0.52    inference(resolution,[],[f112,f52])).
% 1.26/0.52  fof(f52,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.26/0.52    inference(cnf_transformation,[],[f22])).
% 1.26/0.52  fof(f22,plain,(
% 1.26/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.26/0.52    inference(ennf_transformation,[],[f6])).
% 1.26/0.52  fof(f6,axiom,(
% 1.26/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.26/0.52  fof(f112,plain,(
% 1.26/0.52    ~v1_relat_1(sK3) | spl7_9),
% 1.26/0.52    inference(avatar_component_clause,[],[f111])).
% 1.26/0.52  fof(f116,plain,(
% 1.26/0.52    ~spl7_9 | spl7_10 | ~spl7_8),
% 1.26/0.52    inference(avatar_split_clause,[],[f108,f105,f114,f111])).
% 1.26/0.52  fof(f108,plain,(
% 1.26/0.52    ( ! [X0] : (r2_hidden(sK0,X0) | ~v5_relat_1(sK3,X0) | ~v1_relat_1(sK3)) ) | ~spl7_8),
% 1.26/0.52    inference(resolution,[],[f106,f50])).
% 1.26/0.52  fof(f50,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_relat_1(X1)) | r2_hidden(X2,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f20])).
% 1.26/0.52  fof(f20,plain,(
% 1.26/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.26/0.52    inference(flattening,[],[f19])).
% 1.26/0.52  fof(f19,plain,(
% 1.26/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.26/0.52    inference(ennf_transformation,[],[f3])).
% 1.26/0.52  fof(f3,axiom,(
% 1.26/0.52    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(X2,X0)))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).
% 1.26/0.52  fof(f107,plain,(
% 1.26/0.52    spl7_8 | ~spl7_1 | ~spl7_6),
% 1.26/0.52    inference(avatar_split_clause,[],[f99,f95,f72,f105])).
% 1.26/0.52  fof(f72,plain,(
% 1.26/0.52    spl7_1 <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.26/0.52  fof(f95,plain,(
% 1.26/0.52    spl7_6 <=> k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.26/0.52  fof(f99,plain,(
% 1.26/0.52    r2_hidden(sK0,k2_relat_1(sK3)) | (~spl7_1 | ~spl7_6)),
% 1.26/0.52    inference(superposition,[],[f73,f96])).
% 1.26/0.52  fof(f96,plain,(
% 1.26/0.52    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) | ~spl7_6),
% 1.26/0.52    inference(avatar_component_clause,[],[f95])).
% 1.26/0.52  fof(f73,plain,(
% 1.26/0.52    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) | ~spl7_1),
% 1.26/0.52    inference(avatar_component_clause,[],[f72])).
% 1.26/0.52  fof(f97,plain,(
% 1.26/0.52    spl7_6 | ~spl7_2),
% 1.26/0.52    inference(avatar_split_clause,[],[f92,f76,f95])).
% 1.26/0.52  fof(f92,plain,(
% 1.26/0.52    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) | ~spl7_2),
% 1.26/0.52    inference(resolution,[],[f54,f77])).
% 1.26/0.52  fof(f54,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f24])).
% 1.26/0.52  fof(f24,plain,(
% 1.26/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.26/0.52    inference(ennf_transformation,[],[f9])).
% 1.26/0.52  fof(f9,axiom,(
% 1.26/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.26/0.52  fof(f86,plain,(
% 1.26/0.52    spl7_4),
% 1.26/0.52    inference(avatar_split_clause,[],[f37,f84])).
% 1.26/0.52  fof(f37,plain,(
% 1.26/0.52    v1_funct_1(sK3)),
% 1.26/0.52    inference(cnf_transformation,[],[f29])).
% 1.26/0.52  fof(f82,plain,(
% 1.26/0.52    spl7_3),
% 1.26/0.52    inference(avatar_split_clause,[],[f38,f80])).
% 1.26/0.52  fof(f38,plain,(
% 1.26/0.52    v1_funct_2(sK3,sK1,sK2)),
% 1.26/0.52    inference(cnf_transformation,[],[f29])).
% 1.26/0.52  fof(f78,plain,(
% 1.26/0.52    spl7_2),
% 1.26/0.52    inference(avatar_split_clause,[],[f39,f76])).
% 1.26/0.52  fof(f39,plain,(
% 1.26/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.26/0.52    inference(cnf_transformation,[],[f29])).
% 1.26/0.52  fof(f74,plain,(
% 1.26/0.52    spl7_1),
% 1.26/0.52    inference(avatar_split_clause,[],[f40,f72])).
% 1.26/0.52  fof(f40,plain,(
% 1.26/0.52    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 1.26/0.52    inference(cnf_transformation,[],[f29])).
% 1.26/0.52  % SZS output end Proof for theBenchmark
% 1.26/0.52  % (31952)------------------------------
% 1.26/0.52  % (31952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.52  % (31952)Termination reason: Refutation
% 1.26/0.52  
% 1.26/0.52  % (31952)Memory used [KB]: 10874
% 1.26/0.52  % (31952)Time elapsed: 0.067 s
% 1.26/0.52  % (31952)------------------------------
% 1.26/0.52  % (31952)------------------------------
% 1.26/0.52  % (31945)Success in time 0.162 s
%------------------------------------------------------------------------------
