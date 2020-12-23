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
% DateTime   : Thu Dec  3 13:07:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 177 expanded)
%              Number of leaves         :   25 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :  348 ( 605 expanded)
%              Number of equality atoms :   36 (  71 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f260,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f64,f68,f74,f82,f85,f101,f108,f122,f139,f155,f237,f257,f259])).

fof(f259,plain,
    ( ~ spl5_2
    | ~ spl5_27 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f63,f255])).

fof(f255,plain,
    ( ! [X2] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl5_27
  <=> ! [X2] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f63,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl5_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f257,plain,
    ( ~ spl5_5
    | ~ spl5_17
    | spl5_27
    | spl5_8
    | spl5_16 ),
    inference(avatar_split_clause,[],[f251,f137,f96,f254,f145,f77])).

fof(f77,plain,
    ( spl5_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f145,plain,
    ( spl5_17
  <=> r2_hidden(sK0,k9_relat_1(sK3,k1_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f96,plain,
    ( spl5_8
  <=> ! [X3,X2] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f137,plain,
    ( spl5_16
  <=> m1_subset_1(sK4(sK0,k1_relat_1(sK3),sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f251,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X5)))
        | ~ r2_hidden(sK0,k9_relat_1(sK3,k1_relat_1(sK3)))
        | ~ v1_relat_1(sK3) )
    | spl5_16 ),
    inference(resolution,[],[f185,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
            & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
        & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f185,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(sK4(sK0,k1_relat_1(sK3),sK3),k1_relat_1(X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X3))) )
    | spl5_16 ),
    inference(resolution,[],[f179,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f179,plain,
    ( ! [X2,X0,X1] :
        ( ~ v4_relat_1(X0,sK1)
        | ~ r2_hidden(sK4(sK0,k1_relat_1(sK3),sK3),k1_relat_1(X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
    | spl5_16 ),
    inference(resolution,[],[f167,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f167,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | ~ v4_relat_1(X1,sK1)
        | ~ r2_hidden(sK4(sK0,k1_relat_1(sK3),sK3),k1_relat_1(X1)) )
    | spl5_16 ),
    inference(resolution,[],[f164,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f164,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r2_hidden(sK4(sK0,k1_relat_1(sK3),sK3),X0) )
    | spl5_16 ),
    inference(resolution,[],[f140,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f140,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ r2_hidden(sK4(sK0,k1_relat_1(sK3),sK3),X0) )
    | spl5_16 ),
    inference(resolution,[],[f138,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f138,plain,
    ( ~ m1_subset_1(sK4(sK0,k1_relat_1(sK3),sK3),sK1)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f137])).

fof(f237,plain,
    ( ~ spl5_5
    | ~ spl5_4
    | spl5_17 ),
    inference(avatar_split_clause,[],[f230,f145,f72,f77])).

fof(f72,plain,
    ( spl5_4
  <=> r2_hidden(sK0,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f230,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl5_17 ),
    inference(superposition,[],[f146,f40])).

fof(f40,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f146,plain,
    ( ~ r2_hidden(sK0,k9_relat_1(sK3,k1_relat_1(sK3)))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f145])).

fof(f155,plain,
    ( ~ spl5_2
    | ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f63,f97])).

fof(f97,plain,
    ( ! [X2,X3] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f139,plain,
    ( ~ spl5_16
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f128,f120,f137])).

fof(f120,plain,
    ( spl5_13
  <=> sK0 = k1_funct_1(sK3,sK4(sK0,k1_relat_1(sK3),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f128,plain,
    ( ~ m1_subset_1(sK4(sK0,k1_relat_1(sK3),sK3),sK1)
    | ~ spl5_13 ),
    inference(trivial_inequality_removal,[],[f127])).

fof(f127,plain,
    ( sK0 != sK0
    | ~ m1_subset_1(sK4(sK0,k1_relat_1(sK3),sK3),sK1)
    | ~ spl5_13 ),
    inference(superposition,[],[f39,f121])).

fof(f121,plain,
    ( sK0 = k1_funct_1(sK3,sK4(sK0,k1_relat_1(sK3),sK3))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f120])).

fof(f39,plain,(
    ! [X4] :
      ( sK0 != k1_funct_1(sK3,X4)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ! [X4] :
        ( sK0 != k1_funct_1(sK3,X4)
        | ~ m1_subset_1(X4,sK1) )
    & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f26])).

fof(f26,plain,
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

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

fof(f122,plain,
    ( spl5_13
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f110,f106,f72,f120])).

fof(f106,plain,
    ( spl5_10
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | k1_funct_1(sK3,sK4(X0,k1_relat_1(sK3),sK3)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f110,plain,
    ( sK0 = k1_funct_1(sK3,sK4(sK0,k1_relat_1(sK3),sK3))
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(resolution,[],[f107,f73])).

fof(f73,plain,
    ( r2_hidden(sK0,k2_relat_1(sK3))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | k1_funct_1(sK3,sK4(X0,k1_relat_1(sK3),sK3)) = X0 )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f106])).

fof(f108,plain,
    ( ~ spl5_5
    | spl5_10
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f104,f99,f106,f77])).

fof(f99,plain,
    ( spl5_9
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | k1_funct_1(sK3,sK4(X0,X1,sK3)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | k1_funct_1(sK3,sK4(X0,k1_relat_1(sK3),sK3)) = X0
        | ~ v1_relat_1(sK3) )
    | ~ spl5_9 ),
    inference(superposition,[],[f100,f40])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | k1_funct_1(sK3,sK4(X0,X1,sK3)) = X0 )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f99])).

fof(f101,plain,
    ( spl5_8
    | spl5_9
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f94,f80,f99,f96])).

fof(f80,plain,
    ( spl5_6
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
        | k1_funct_1(sK3,X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f94,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k1_funct_1(sK3,sK4(X0,X1,sK3)) = X0 )
    | ~ spl5_6 ),
    inference(resolution,[],[f86,f81])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
        | k1_funct_1(sK3,X0) = X1 )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X2,X1),X0),X1)
      | ~ r2_hidden(X0,k9_relat_1(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(resolution,[],[f46,f49])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f85,plain,
    ( ~ spl5_2
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | ~ spl5_2
    | spl5_5 ),
    inference(subsumption_resolution,[],[f63,f83])).

fof(f83,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_5 ),
    inference(resolution,[],[f78,f49])).

fof(f78,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f82,plain,
    ( ~ spl5_5
    | spl5_6
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f75,f66,f80,f77])).

fof(f66,plain,
    ( spl5_3
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
        | k1_funct_1(sK3,X0) = X1
        | ~ v1_relat_1(sK3) )
    | ~ spl5_3 ),
    inference(resolution,[],[f53,f67])).

fof(f67,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f74,plain,
    ( ~ spl5_2
    | spl5_4
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f69,f58,f72,f62])).

fof(f58,plain,
    ( spl5_1
  <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f69,plain,
    ( r2_hidden(sK0,k2_relat_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_1 ),
    inference(superposition,[],[f59,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f59,plain,
    ( r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f68,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f36,f66])).

fof(f36,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f64,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f37,f62])).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f38,f58])).

fof(f38,plain,(
    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:03:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (17431)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (17440)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (17432)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (17439)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (17439)Refutation not found, incomplete strategy% (17439)------------------------------
% 0.21/0.49  % (17439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (17439)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (17439)Memory used [KB]: 1663
% 0.21/0.49  % (17439)Time elapsed: 0.071 s
% 0.21/0.49  % (17439)------------------------------
% 0.21/0.49  % (17439)------------------------------
% 0.21/0.50  % (17433)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (17430)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (17432)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f260,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f60,f64,f68,f74,f82,f85,f101,f108,f122,f139,f155,f237,f257,f259])).
% 0.21/0.50  fof(f259,plain,(
% 0.21/0.50    ~spl5_2 | ~spl5_27),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f258])).
% 0.21/0.50  fof(f258,plain,(
% 0.21/0.50    $false | (~spl5_2 | ~spl5_27)),
% 0.21/0.50    inference(subsumption_resolution,[],[f63,f255])).
% 0.21/0.50  fof(f255,plain,(
% 0.21/0.50    ( ! [X2] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))) ) | ~spl5_27),
% 0.21/0.50    inference(avatar_component_clause,[],[f254])).
% 0.21/0.50  fof(f254,plain,(
% 0.21/0.50    spl5_27 <=> ! [X2] : ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    spl5_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.50  fof(f257,plain,(
% 0.21/0.50    ~spl5_5 | ~spl5_17 | spl5_27 | spl5_8 | spl5_16),
% 0.21/0.50    inference(avatar_split_clause,[],[f251,f137,f96,f254,f145,f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    spl5_5 <=> v1_relat_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    spl5_17 <=> r2_hidden(sK0,k9_relat_1(sK3,k1_relat_1(sK3)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    spl5_8 <=> ! [X3,X2] : ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    spl5_16 <=> m1_subset_1(sK4(sK0,k1_relat_1(sK3),sK3),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.50  fof(f251,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X5))) | ~r2_hidden(sK0,k9_relat_1(sK3,k1_relat_1(sK3))) | ~v1_relat_1(sK3)) ) | spl5_16),
% 0.21/0.50    inference(resolution,[],[f185,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(rectify,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(nnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK4(sK0,k1_relat_1(sK3),sK3),k1_relat_1(X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X3)))) ) | spl5_16),
% 0.21/0.50    inference(resolution,[],[f179,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.50    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.50  fof(f179,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v4_relat_1(X0,sK1) | ~r2_hidden(sK4(sK0,k1_relat_1(sK3),sK3),k1_relat_1(X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ) | spl5_16),
% 0.21/0.50    inference(resolution,[],[f167,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    ( ! [X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,sK1) | ~r2_hidden(sK4(sK0,k1_relat_1(sK3),sK3),k1_relat_1(X1))) ) | spl5_16),
% 0.21/0.50    inference(resolution,[],[f164,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(X0,sK1) | ~r2_hidden(sK4(sK0,k1_relat_1(sK3),sK3),X0)) ) | spl5_16),
% 0.21/0.50    inference(resolution,[],[f140,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~r2_hidden(sK4(sK0,k1_relat_1(sK3),sK3),X0)) ) | spl5_16),
% 0.21/0.50    inference(resolution,[],[f138,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    ~m1_subset_1(sK4(sK0,k1_relat_1(sK3),sK3),sK1) | spl5_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f137])).
% 0.21/0.50  fof(f237,plain,(
% 0.21/0.50    ~spl5_5 | ~spl5_4 | spl5_17),
% 0.21/0.50    inference(avatar_split_clause,[],[f230,f145,f72,f77])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    spl5_4 <=> r2_hidden(sK0,k2_relat_1(sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.50  fof(f230,plain,(
% 0.21/0.50    ~r2_hidden(sK0,k2_relat_1(sK3)) | ~v1_relat_1(sK3) | spl5_17),
% 0.21/0.50    inference(superposition,[],[f146,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    ~r2_hidden(sK0,k9_relat_1(sK3,k1_relat_1(sK3))) | spl5_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f145])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    ~spl5_2 | ~spl5_8),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f154])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    $false | (~spl5_2 | ~spl5_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f63,f97])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) | ~spl5_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f96])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    ~spl5_16 | ~spl5_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f128,f120,f137])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    spl5_13 <=> sK0 = k1_funct_1(sK3,sK4(sK0,k1_relat_1(sK3),sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    ~m1_subset_1(sK4(sK0,k1_relat_1(sK3),sK3),sK1) | ~spl5_13),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f127])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    sK0 != sK0 | ~m1_subset_1(sK4(sK0,k1_relat_1(sK3),sK3),sK1) | ~spl5_13),
% 0.21/0.50    inference(superposition,[],[f39,f121])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    sK0 = k1_funct_1(sK3,sK4(sK0,k1_relat_1(sK3),sK3)) | ~spl5_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f120])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)) => (! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3))),
% 0.21/0.50    inference(flattening,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.21/0.50    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.50  fof(f11,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.21/0.50    inference(negated_conjecture,[],[f10])).
% 0.21/0.50  fof(f10,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    spl5_13 | ~spl5_4 | ~spl5_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f110,f106,f72,f120])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    spl5_10 <=> ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | k1_funct_1(sK3,sK4(X0,k1_relat_1(sK3),sK3)) = X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    sK0 = k1_funct_1(sK3,sK4(sK0,k1_relat_1(sK3),sK3)) | (~spl5_4 | ~spl5_10)),
% 0.21/0.50    inference(resolution,[],[f107,f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    r2_hidden(sK0,k2_relat_1(sK3)) | ~spl5_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f72])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | k1_funct_1(sK3,sK4(X0,k1_relat_1(sK3),sK3)) = X0) ) | ~spl5_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f106])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    ~spl5_5 | spl5_10 | ~spl5_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f104,f99,f106,f77])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    spl5_9 <=> ! [X1,X0] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | k1_funct_1(sK3,sK4(X0,X1,sK3)) = X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | k1_funct_1(sK3,sK4(X0,k1_relat_1(sK3),sK3)) = X0 | ~v1_relat_1(sK3)) ) | ~spl5_9),
% 0.21/0.50    inference(superposition,[],[f100,f40])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | k1_funct_1(sK3,sK4(X0,X1,sK3)) = X0) ) | ~spl5_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f99])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    spl5_8 | spl5_9 | ~spl5_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f94,f80,f99,f96])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    spl5_6 <=> ! [X1,X0] : (~r2_hidden(k4_tarski(X0,X1),sK3) | k1_funct_1(sK3,X0) = X1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_funct_1(sK3,sK4(X0,X1,sK3)) = X0) ) | ~spl5_6),
% 0.21/0.50    inference(resolution,[],[f86,f81])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK3) | k1_funct_1(sK3,X0) = X1) ) | ~spl5_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f80])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK4(X0,X2,X1),X0),X1) | ~r2_hidden(X0,k9_relat_1(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.21/0.50    inference(resolution,[],[f46,f49])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ~spl5_2 | spl5_5),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f84])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    $false | (~spl5_2 | spl5_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f63,f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl5_5),
% 0.21/0.50    inference(resolution,[],[f78,f49])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ~v1_relat_1(sK3) | spl5_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f77])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ~spl5_5 | spl5_6 | ~spl5_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f75,f66,f80,f77])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    spl5_3 <=> v1_funct_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK3) | k1_funct_1(sK3,X0) = X1 | ~v1_relat_1(sK3)) ) | ~spl5_3),
% 0.21/0.50    inference(resolution,[],[f53,f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    v1_funct_1(sK3) | ~spl5_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f66])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(nnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ~spl5_2 | spl5_4 | ~spl5_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f69,f58,f72,f62])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    spl5_1 <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    r2_hidden(sK0,k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_1),
% 0.21/0.50    inference(superposition,[],[f59,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) | ~spl5_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f58])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    spl5_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f36,f66])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    v1_funct_1(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    spl5_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f37,f62])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    spl5_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f38,f58])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (17432)------------------------------
% 0.21/0.50  % (17432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (17432)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (17432)Memory used [KB]: 10746
% 0.21/0.50  % (17432)Time elapsed: 0.032 s
% 0.21/0.50  % (17432)------------------------------
% 0.21/0.50  % (17432)------------------------------
% 0.21/0.50  % (17425)Success in time 0.142 s
%------------------------------------------------------------------------------
