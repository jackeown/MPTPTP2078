%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 189 expanded)
%              Number of leaves         :   30 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :  358 ( 613 expanded)
%              Number of equality atoms :   75 ( 149 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f243,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f70,f74,f78,f109,f118,f153,f154,f172,f189,f190,f211,f220,f229,f235])).

fof(f235,plain,
    ( spl3_20
    | ~ spl3_19
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f232,f227,f209,f218])).

fof(f218,plain,
    ( spl3_20
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f209,plain,
    ( spl3_19
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f227,plain,
    ( spl3_21
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f232,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_19
    | ~ spl3_21 ),
    inference(resolution,[],[f216,f228])).

fof(f228,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f227])).

fof(f216,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X3) )
    | ~ spl3_19 ),
    inference(trivial_inequality_removal,[],[f215])).

fof(f215,plain,
    ( ! [X3] :
        ( k1_xboole_0 != k1_xboole_0
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X3)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3))) )
    | ~ spl3_19 ),
    inference(superposition,[],[f139,f210])).

fof(f210,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f209])).

fof(f139,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(superposition,[],[f57,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f57,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f229,plain,
    ( spl3_21
    | ~ spl3_18
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f224,f209,f187,f227])).

fof(f187,plain,
    ( spl3_18
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f224,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_18
    | ~ spl3_19 ),
    inference(superposition,[],[f188,f210])).

fof(f188,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f187])).

fof(f220,plain,
    ( ~ spl3_20
    | spl3_15
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f212,f209,f170,f218])).

fof(f170,plain,
    ( spl3_15
  <=> v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f212,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl3_15
    | ~ spl3_19 ),
    inference(superposition,[],[f171,f210])).

fof(f171,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | spl3_15 ),
    inference(avatar_component_clause,[],[f170])).

fof(f211,plain,
    ( ~ spl3_18
    | spl3_19
    | spl3_15 ),
    inference(avatar_split_clause,[],[f206,f170,f209,f187])).

fof(f206,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | spl3_15 ),
    inference(resolution,[],[f171,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f190,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_relat_1(sK0)
    | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f189,plain,
    ( spl3_18
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f185,f157,f113,f66,f187])).

fof(f66,plain,
    ( spl3_3
  <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f113,plain,
    ( spl3_8
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f157,plain,
    ( spl3_14
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f185,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f167,f158])).

fof(f158,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f157])).

fof(f167,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))))
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(superposition,[],[f108,f114])).

fof(f114,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f108,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f172,plain,
    ( ~ spl3_15
    | spl3_2
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f168,f157,f113,f63,f170])).

fof(f63,plain,
    ( spl3_2
  <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f168,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | spl3_2
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f160,f158])).

fof(f160,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))
    | spl3_2
    | ~ spl3_8 ),
    inference(superposition,[],[f64,f114])).

fof(f64,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f154,plain,
    ( k1_xboole_0 != k2_relat_1(sK0)
    | v1_xboole_0(k2_relat_1(sK0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f153,plain,
    ( spl3_2
    | spl3_13
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f147,f66,f151,f63])).

fof(f151,plain,
    ( spl3_13
  <=> k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f147,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl3_3 ),
    inference(resolution,[],[f146,f108])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
      | k1_xboole_0 = X1
      | v1_funct_2(X0,k1_relat_1(X0),X1) ) ),
    inference(equality_resolution,[],[f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f50,f47])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f118,plain,
    ( spl3_8
    | ~ spl3_9
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f110,f66,f116,f113])).

fof(f116,plain,
    ( spl3_9
  <=> v1_xboole_0(k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f110,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK0))
    | k1_xboole_0 = sK0
    | ~ spl3_3 ),
    inference(resolution,[],[f108,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_xboole_0(X2)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f44,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f41,f39])).

fof(f39,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f109,plain,
    ( spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f107,f72,f66])).

fof(f72,plain,
    ( spl3_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f107,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ spl3_4 ),
    inference(resolution,[],[f106,f79])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f38,f37])).

fof(f37,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f106,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_relat_1(sK0),k1_zfmisc_1(X0))
        | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK0)))) )
    | ~ spl3_4 ),
    inference(resolution,[],[f105,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f105,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK0),X0)
        | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK0)))) )
    | ~ spl3_4 ),
    inference(resolution,[],[f104,f79])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k2_relat_1(sK0),k1_zfmisc_1(X1))
        | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_tarski(k1_relat_1(sK0),X0) )
    | ~ spl3_4 ),
    inference(resolution,[],[f103,f45])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK0),X0)
        | ~ r1_tarski(k1_relat_1(sK0),X1)
        | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl3_4 ),
    inference(resolution,[],[f46,f73])).

fof(f73,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f78,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f36,f76])).

fof(f76,plain,
    ( spl3_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f74,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f33,f72])).

fof(f33,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
      | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
      | ~ v1_funct_1(sK0) )
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          | ~ v1_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
        | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
        | ~ v1_funct_1(sK0) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f70,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f34,f60])).

fof(f60,plain,
    ( spl3_1
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f34,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f35,f66,f63,f60])).

fof(f35,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:52:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (8331)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (8339)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (8339)Refutation not found, incomplete strategy% (8339)------------------------------
% 0.22/0.50  % (8339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (8339)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (8339)Memory used [KB]: 1663
% 0.22/0.50  % (8339)Time elapsed: 0.075 s
% 0.22/0.50  % (8339)------------------------------
% 0.22/0.50  % (8339)------------------------------
% 0.22/0.51  % (8336)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.51  % (8330)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (8336)Refutation not found, incomplete strategy% (8336)------------------------------
% 0.22/0.51  % (8336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (8336)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (8336)Memory used [KB]: 6140
% 0.22/0.51  % (8336)Time elapsed: 0.075 s
% 0.22/0.51  % (8336)------------------------------
% 0.22/0.51  % (8336)------------------------------
% 0.22/0.51  % (8326)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (8327)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (8327)Refutation not found, incomplete strategy% (8327)------------------------------
% 0.22/0.52  % (8327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (8327)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (8327)Memory used [KB]: 10618
% 0.22/0.52  % (8327)Time elapsed: 0.093 s
% 0.22/0.52  % (8327)------------------------------
% 0.22/0.52  % (8327)------------------------------
% 0.22/0.52  % (8338)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (8328)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.52  % (8338)Refutation not found, incomplete strategy% (8338)------------------------------
% 0.22/0.52  % (8338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (8338)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (8338)Memory used [KB]: 6140
% 0.22/0.52  % (8338)Time elapsed: 0.094 s
% 0.22/0.52  % (8338)------------------------------
% 0.22/0.52  % (8338)------------------------------
% 0.22/0.53  % (8345)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.53  % (8345)Refutation not found, incomplete strategy% (8345)------------------------------
% 0.22/0.53  % (8345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (8345)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (8345)Memory used [KB]: 6140
% 0.22/0.53  % (8345)Time elapsed: 0.099 s
% 0.22/0.53  % (8345)------------------------------
% 0.22/0.53  % (8345)------------------------------
% 0.22/0.53  % (8340)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.53  % (8332)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.53  % (8326)Refutation not found, incomplete strategy% (8326)------------------------------
% 0.22/0.53  % (8326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (8326)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (8326)Memory used [KB]: 6140
% 0.22/0.53  % (8326)Time elapsed: 0.101 s
% 0.22/0.53  % (8326)------------------------------
% 0.22/0.53  % (8326)------------------------------
% 0.22/0.53  % (8337)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.54  % (8337)Refutation not found, incomplete strategy% (8337)------------------------------
% 0.22/0.54  % (8337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (8337)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (8337)Memory used [KB]: 10618
% 0.22/0.54  % (8337)Time elapsed: 0.088 s
% 0.22/0.54  % (8337)------------------------------
% 0.22/0.54  % (8337)------------------------------
% 0.22/0.54  % (8332)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f243,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f68,f70,f74,f78,f109,f118,f153,f154,f172,f189,f190,f211,f220,f229,f235])).
% 0.22/0.54  fof(f235,plain,(
% 0.22/0.54    spl3_20 | ~spl3_19 | ~spl3_21),
% 0.22/0.54    inference(avatar_split_clause,[],[f232,f227,f209,f218])).
% 0.22/0.54  fof(f218,plain,(
% 0.22/0.54    spl3_20 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.54  fof(f209,plain,(
% 0.22/0.54    spl3_19 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.54  fof(f227,plain,(
% 0.22/0.54    spl3_21 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.54  fof(f232,plain,(
% 0.22/0.54    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl3_19 | ~spl3_21)),
% 0.22/0.54    inference(resolution,[],[f216,f228])).
% 0.22/0.54  fof(f228,plain,(
% 0.22/0.54    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl3_21),
% 0.22/0.54    inference(avatar_component_clause,[],[f227])).
% 0.22/0.54  fof(f216,plain,(
% 0.22/0.54    ( ! [X3] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3))) | v1_funct_2(k1_xboole_0,k1_xboole_0,X3)) ) | ~spl3_19),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f215])).
% 0.22/0.54  fof(f215,plain,(
% 0.22/0.54    ( ! [X3] : (k1_xboole_0 != k1_xboole_0 | v1_funct_2(k1_xboole_0,k1_xboole_0,X3) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))) ) | ~spl3_19),
% 0.22/0.54    inference(superposition,[],[f139,f210])).
% 0.22/0.54  fof(f210,plain,(
% 0.22/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_19),
% 0.22/0.54    inference(avatar_component_clause,[],[f209])).
% 0.22/0.54  fof(f139,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f138])).
% 0.22/0.54  fof(f138,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 0.22/0.54    inference(superposition,[],[f57,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.22/0.54    inference(equality_resolution,[],[f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(nnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(flattening,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.54  fof(f229,plain,(
% 0.22/0.54    spl3_21 | ~spl3_18 | ~spl3_19),
% 0.22/0.54    inference(avatar_split_clause,[],[f224,f209,f187,f227])).
% 0.22/0.54  fof(f187,plain,(
% 0.22/0.54    spl3_18 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.54  fof(f224,plain,(
% 0.22/0.54    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_18 | ~spl3_19)),
% 0.22/0.54    inference(superposition,[],[f188,f210])).
% 0.22/0.54  fof(f188,plain,(
% 0.22/0.54    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~spl3_18),
% 0.22/0.54    inference(avatar_component_clause,[],[f187])).
% 0.22/0.54  fof(f220,plain,(
% 0.22/0.54    ~spl3_20 | spl3_15 | ~spl3_19),
% 0.22/0.54    inference(avatar_split_clause,[],[f212,f209,f170,f218])).
% 0.22/0.54  fof(f170,plain,(
% 0.22/0.54    spl3_15 <=> v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.54  fof(f212,plain,(
% 0.22/0.54    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl3_15 | ~spl3_19)),
% 0.22/0.54    inference(superposition,[],[f171,f210])).
% 0.22/0.54  fof(f171,plain,(
% 0.22/0.54    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | spl3_15),
% 0.22/0.54    inference(avatar_component_clause,[],[f170])).
% 0.22/0.54  fof(f211,plain,(
% 0.22/0.54    ~spl3_18 | spl3_19 | spl3_15),
% 0.22/0.54    inference(avatar_split_clause,[],[f206,f170,f209,f187])).
% 0.22/0.54  fof(f206,plain,(
% 0.22/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | spl3_15),
% 0.22/0.54    inference(resolution,[],[f171,f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.22/0.54    inference(equality_resolution,[],[f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(equality_resolution,[],[f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f190,plain,(
% 0.22/0.54    k1_xboole_0 != sK0 | k1_xboole_0 != k2_relat_1(sK0) | k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.54  fof(f189,plain,(
% 0.22/0.54    spl3_18 | ~spl3_3 | ~spl3_8 | ~spl3_14),
% 0.22/0.54    inference(avatar_split_clause,[],[f185,f157,f113,f66,f187])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    spl3_3 <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.54  fof(f113,plain,(
% 0.22/0.54    spl3_8 <=> k1_xboole_0 = sK0),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.54  fof(f157,plain,(
% 0.22/0.54    spl3_14 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.54  fof(f185,plain,(
% 0.22/0.54    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | (~spl3_3 | ~spl3_8 | ~spl3_14)),
% 0.22/0.54    inference(forward_demodulation,[],[f167,f158])).
% 0.22/0.54  fof(f158,plain,(
% 0.22/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl3_14),
% 0.22/0.54    inference(avatar_component_clause,[],[f157])).
% 0.22/0.54  fof(f167,plain,(
% 0.22/0.54    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)))) | (~spl3_3 | ~spl3_8)),
% 0.22/0.54    inference(superposition,[],[f108,f114])).
% 0.22/0.54  fof(f114,plain,(
% 0.22/0.54    k1_xboole_0 = sK0 | ~spl3_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f113])).
% 0.22/0.54  fof(f108,plain,(
% 0.22/0.54    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~spl3_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f66])).
% 0.22/0.54  fof(f172,plain,(
% 0.22/0.54    ~spl3_15 | spl3_2 | ~spl3_8 | ~spl3_14),
% 0.22/0.54    inference(avatar_split_clause,[],[f168,f157,f113,f63,f170])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    spl3_2 <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.54  fof(f168,plain,(
% 0.22/0.54    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (spl3_2 | ~spl3_8 | ~spl3_14)),
% 0.22/0.54    inference(forward_demodulation,[],[f160,f158])).
% 0.22/0.54  fof(f160,plain,(
% 0.22/0.54    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) | (spl3_2 | ~spl3_8)),
% 0.22/0.54    inference(superposition,[],[f64,f114])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | spl3_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f63])).
% 0.22/0.54  fof(f154,plain,(
% 0.22/0.54    k1_xboole_0 != k2_relat_1(sK0) | v1_xboole_0(k2_relat_1(sK0)) | ~v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.54  fof(f153,plain,(
% 0.22/0.54    spl3_2 | spl3_13 | ~spl3_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f147,f66,f151,f63])).
% 0.22/0.54  fof(f151,plain,(
% 0.22/0.54    spl3_13 <=> k1_xboole_0 = k2_relat_1(sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.54  fof(f147,plain,(
% 0.22/0.54    k1_xboole_0 = k2_relat_1(sK0) | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~spl3_3),
% 0.22/0.54    inference(resolution,[],[f146,f108])).
% 0.22/0.54  fof(f146,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) | k1_xboole_0 = X1 | v1_funct_2(X0,k1_relat_1(X0),X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f145])).
% 0.22/0.54  fof(f145,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k1_relat_1(X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f144])).
% 0.22/0.54  fof(f144,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k1_relat_1(X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(superposition,[],[f50,f47])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f118,plain,(
% 0.22/0.54    spl3_8 | ~spl3_9 | ~spl3_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f110,f66,f116,f113])).
% 0.22/0.54  fof(f116,plain,(
% 0.22/0.54    spl3_9 <=> v1_xboole_0(k2_relat_1(sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    ~v1_xboole_0(k2_relat_1(sK0)) | k1_xboole_0 = sK0 | ~spl3_3),
% 0.22/0.54    inference(resolution,[],[f108,f84])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_xboole_0(X2) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(resolution,[],[f44,f80])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(resolution,[],[f41,f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.54    inference(rectify,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.54    inference(nnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)) | k1_xboole_0 = X0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    spl3_3 | ~spl3_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f107,f72,f66])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    spl3_4 <=> v1_relat_1(sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.54  fof(f107,plain,(
% 0.22/0.54    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~spl3_4),
% 0.22/0.54    inference(resolution,[],[f106,f79])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(forward_demodulation,[],[f38,f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(k1_relat_1(sK0),k1_zfmisc_1(X0)) | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK0))))) ) | ~spl3_4),
% 0.22/0.54    inference(resolution,[],[f105,f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.22/0.54    inference(unused_predicate_definition_removal,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.54  fof(f105,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(k1_relat_1(sK0),X0) | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK0))))) ) | ~spl3_4),
% 0.22/0.54    inference(resolution,[],[f104,f79])).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(k2_relat_1(sK0),k1_zfmisc_1(X1)) | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(sK0),X0)) ) | ~spl3_4),
% 0.22/0.54    inference(resolution,[],[f103,f45])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK0),X0) | ~r1_tarski(k1_relat_1(sK0),X1) | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | ~spl3_4),
% 0.22/0.54    inference(resolution,[],[f46,f73])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    v1_relat_1(sK0) | ~spl3_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f72])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(flattening,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    spl3_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f36,f76])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    spl3_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    spl3_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f33,f72])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    v1_relat_1(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    (~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,negated_conjecture,(
% 0.22/0.54    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.54    inference(negated_conjecture,[],[f11])).
% 0.22/0.54  fof(f11,conjecture,(
% 0.22/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    spl3_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f34,f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    spl3_1 <=> v1_funct_1(sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    v1_funct_1(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f35,f66,f63,f60])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (8332)------------------------------
% 0.22/0.54  % (8332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (8332)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (8332)Memory used [KB]: 10746
% 0.22/0.54  % (8332)Time elapsed: 0.108 s
% 0.22/0.54  % (8332)------------------------------
% 0.22/0.54  % (8332)------------------------------
% 0.22/0.54  % (8346)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.54  % (8341)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.54  % (8334)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.54  % (8335)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.54  % (8346)Refutation not found, incomplete strategy% (8346)------------------------------
% 0.22/0.54  % (8346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (8346)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (8346)Memory used [KB]: 10490
% 0.22/0.54  % (8346)Time elapsed: 0.109 s
% 0.22/0.54  % (8346)------------------------------
% 0.22/0.54  % (8346)------------------------------
% 0.22/0.54  % (8341)Refutation not found, incomplete strategy% (8341)------------------------------
% 0.22/0.54  % (8341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (8341)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (8341)Memory used [KB]: 6140
% 0.22/0.54  % (8341)Time elapsed: 0.071 s
% 0.22/0.54  % (8341)------------------------------
% 0.22/0.54  % (8341)------------------------------
% 0.22/0.55  % (8329)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (8344)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.55  % (8329)Refutation not found, incomplete strategy% (8329)------------------------------
% 0.22/0.55  % (8329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (8329)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (8329)Memory used [KB]: 10618
% 0.22/0.55  % (8329)Time elapsed: 0.121 s
% 0.22/0.55  % (8329)------------------------------
% 0.22/0.55  % (8329)------------------------------
% 0.22/0.55  % (8343)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.55  % (8342)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.56  % (8325)Success in time 0.188 s
%------------------------------------------------------------------------------
