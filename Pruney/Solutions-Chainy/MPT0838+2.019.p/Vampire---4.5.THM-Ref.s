%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 184 expanded)
%              Number of leaves         :   31 (  77 expanded)
%              Depth                    :   10
%              Number of atoms          :  341 ( 571 expanded)
%              Number of equality atoms :   74 ( 114 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f209,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f80,f85,f93,f99,f106,f122,f141,f148,f152,f158,f164,f170,f178,f186,f208])).

fof(f208,plain,
    ( ~ spl4_7
    | ~ spl4_10
    | spl4_15
    | ~ spl4_17 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_10
    | spl4_15
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f199,f121])).

fof(f121,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl4_10
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f199,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ spl4_7
    | spl4_15
    | ~ spl4_17 ),
    inference(backward_demodulation,[],[f163,f193])).

fof(f193,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_7
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f192,f98])).

fof(f98,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_7
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f192,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2)
    | ~ spl4_17 ),
    inference(trivial_inequality_removal,[],[f191])).

fof(f191,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2)
    | ~ spl4_17 ),
    inference(superposition,[],[f45,f174])).

fof(f174,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl4_17
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f163,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl4_15
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f186,plain,
    ( spl4_17
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f181,f176,f167,f172])).

fof(f167,plain,
    ( spl4_16
  <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f176,plain,
    ( spl4_18
  <=> ! [X0] :
        ( ~ m1_subset_1(sK3(X0,k2_relat_1(sK2)),sK1)
        | ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f181,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f180,f169])).

fof(f169,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f167])).

fof(f180,plain,
    ( ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl4_18 ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,
    ( ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl4_18 ),
    inference(resolution,[],[f177,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

fof(f177,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(X0,k2_relat_1(sK2)),sK1)
        | ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(X0)) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f176])).

fof(f178,plain,
    ( spl4_17
    | spl4_18
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f153,f150,f176,f172])).

fof(f150,plain,
    ( spl4_13
  <=> ! [X3] :
        ( ~ r2_hidden(X3,k2_relat_1(sK2))
        | ~ m1_subset_1(X3,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(X0,k2_relat_1(sK2)),sK1)
        | k1_xboole_0 = k2_relat_1(sK2)
        | ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(X0)) )
    | ~ spl4_13 ),
    inference(resolution,[],[f151,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f151,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relat_1(sK2))
        | ~ m1_subset_1(X3,sK1) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f150])).

fof(f170,plain,
    ( spl4_16
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f165,f155,f145,f167])).

fof(f145,plain,
    ( spl4_12
  <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f155,plain,
    ( spl4_14
  <=> m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f165,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f157,f147])).

fof(f147,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f145])).

fof(f157,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f155])).

fof(f164,plain,
    ( ~ spl4_15
    | spl4_5
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f159,f138,f82,f161])).

fof(f82,plain,
    ( spl4_5
  <=> k1_xboole_0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f138,plain,
    ( spl4_11
  <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f159,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl4_5
    | ~ spl4_11 ),
    inference(superposition,[],[f84,f140])).

fof(f140,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f138])).

fof(f84,plain,
    ( k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f158,plain,
    ( spl4_14
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f132,f77,f155])).

fof(f77,plain,
    ( spl4_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f132,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f57,f79])).

fof(f79,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f152,plain,
    ( spl4_13
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f143,f77,f150])).

fof(f143,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relat_1(sK2))
        | ~ m1_subset_1(X3,sK1) )
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f41,f127])).

fof(f127,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f56,f79])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f41,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
        | ~ m1_subset_1(X3,sK1) )
    & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                    | ~ m1_subset_1(X3,X1) )
                & k1_xboole_0 != k1_relset_1(X0,X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(sK0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(sK0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( ~ r2_hidden(X3,k2_relset_1(sK0,X1,X2))
                | ~ m1_subset_1(X3,X1) )
            & k1_xboole_0 != k1_relset_1(sK0,X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,X2))
              | ~ m1_subset_1(X3,sK1) )
          & k1_xboole_0 != k1_relset_1(sK0,sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,X2))
            | ~ m1_subset_1(X3,sK1) )
        & k1_xboole_0 != k1_relset_1(sK0,sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
          | ~ m1_subset_1(X3,sK1) )
      & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                    & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                  & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

fof(f148,plain,
    ( spl4_12
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f127,f77,f145])).

fof(f141,plain,
    ( spl4_11
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f123,f77,f138])).

fof(f123,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f55,f79])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f122,plain,
    ( spl4_10
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f109,f103,f119])).

fof(f103,plain,
    ( spl4_8
  <=> v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f109,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_8 ),
    inference(resolution,[],[f105,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f105,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f106,plain,
    ( spl4_8
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f100,f90,f103])).

fof(f90,plain,
    ( spl4_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f100,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl4_6 ),
    inference(resolution,[],[f92,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f92,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f99,plain,
    ( spl4_7
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f94,f77,f96])).

fof(f94,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f54,f79])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f93,plain,
    ( spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f88,f72,f90])).

fof(f72,plain,
    ( spl4_3
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f88,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f87,f59])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f87,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0)
    | ~ spl4_3 ),
    inference(resolution,[],[f48,f74])).

fof(f74,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f85,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f40,f82])).

fof(f40,plain,(
    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f39,f77])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f75,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f58,f72])).

fof(f58,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:30:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (21713)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.49  % (21709)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.49  % (21710)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  % (21719)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (21709)Refutation not found, incomplete strategy% (21709)------------------------------
% 0.21/0.50  % (21709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (21709)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (21709)Memory used [KB]: 10618
% 0.21/0.50  % (21709)Time elapsed: 0.086 s
% 0.21/0.50  % (21709)------------------------------
% 0.21/0.50  % (21709)------------------------------
% 0.21/0.50  % (21708)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (21710)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (21708)Refutation not found, incomplete strategy% (21708)------------------------------
% 0.21/0.50  % (21708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (21708)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (21708)Memory used [KB]: 10618
% 0.21/0.50  % (21708)Time elapsed: 0.086 s
% 0.21/0.50  % (21708)------------------------------
% 0.21/0.50  % (21708)------------------------------
% 0.21/0.50  % (21716)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.50  % (21724)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.50  % (21714)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (21727)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (21714)Refutation not found, incomplete strategy% (21714)------------------------------
% 0.21/0.51  % (21714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21714)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (21714)Memory used [KB]: 10618
% 0.21/0.51  % (21714)Time elapsed: 0.064 s
% 0.21/0.51  % (21714)------------------------------
% 0.21/0.51  % (21714)------------------------------
% 0.21/0.51  % (21722)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (21726)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (21712)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (21717)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (21730)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (21729)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (21711)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (21732)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (21718)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f75,f80,f85,f93,f99,f106,f122,f141,f148,f152,f158,f164,f170,f178,f186,f208])).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    ~spl4_7 | ~spl4_10 | spl4_15 | ~spl4_17),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f207])).
% 0.21/0.52  fof(f207,plain,(
% 0.21/0.52    $false | (~spl4_7 | ~spl4_10 | spl4_15 | ~spl4_17)),
% 0.21/0.52    inference(subsumption_resolution,[],[f199,f121])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f119])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    spl4_10 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.52  fof(f199,plain,(
% 0.21/0.52    k1_xboole_0 != k1_relat_1(k1_xboole_0) | (~spl4_7 | spl4_15 | ~spl4_17)),
% 0.21/0.52    inference(backward_demodulation,[],[f163,f193])).
% 0.21/0.52  fof(f193,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | (~spl4_7 | ~spl4_17)),
% 0.21/0.52    inference(subsumption_resolution,[],[f192,f98])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    v1_relat_1(sK2) | ~spl4_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    spl4_7 <=> v1_relat_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | ~v1_relat_1(sK2) | ~spl4_17),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f191])).
% 0.21/0.52  fof(f191,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | ~v1_relat_1(sK2) | ~spl4_17),
% 0.21/0.52    inference(superposition,[],[f45,f174])).
% 0.21/0.52  fof(f174,plain,(
% 0.21/0.52    k1_xboole_0 = k2_relat_1(sK2) | ~spl4_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f172])).
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    spl4_17 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    k1_xboole_0 != k1_relat_1(sK2) | spl4_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f161])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    spl4_15 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.52  fof(f186,plain,(
% 0.21/0.52    spl4_17 | ~spl4_16 | ~spl4_18),
% 0.21/0.52    inference(avatar_split_clause,[],[f181,f176,f167,f172])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    spl4_16 <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.52  fof(f176,plain,(
% 0.21/0.52    spl4_18 <=> ! [X0] : (~m1_subset_1(sK3(X0,k2_relat_1(sK2)),sK1) | ~m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(X0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.52  fof(f181,plain,(
% 0.21/0.52    k1_xboole_0 = k2_relat_1(sK2) | (~spl4_16 | ~spl4_18)),
% 0.21/0.52    inference(subsumption_resolution,[],[f180,f169])).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~spl4_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f167])).
% 0.21/0.52  fof(f180,plain,(
% 0.21/0.52    ~m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | k1_xboole_0 = k2_relat_1(sK2) | ~spl4_18),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f179])).
% 0.21/0.52  fof(f179,plain,(
% 0.21/0.52    ~m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | k1_xboole_0 = k2_relat_1(sK2) | ~m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~spl4_18),
% 0.21/0.52    inference(resolution,[],[f177,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),X0) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1] : ((r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(flattening,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK3(X0,k2_relat_1(sK2)),sK1) | ~m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(X0))) ) | ~spl4_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f176])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    spl4_17 | spl4_18 | ~spl4_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f153,f150,f176,f172])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    spl4_13 <=> ! [X3] : (~r2_hidden(X3,k2_relat_1(sK2)) | ~m1_subset_1(X3,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK3(X0,k2_relat_1(sK2)),sK1) | k1_xboole_0 = k2_relat_1(sK2) | ~m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(X0))) ) | ~spl4_13),
% 0.21/0.52    inference(resolution,[],[f151,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    ( ! [X3] : (~r2_hidden(X3,k2_relat_1(sK2)) | ~m1_subset_1(X3,sK1)) ) | ~spl4_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f150])).
% 0.21/0.52  fof(f170,plain,(
% 0.21/0.52    spl4_16 | ~spl4_12 | ~spl4_14),
% 0.21/0.52    inference(avatar_split_clause,[],[f165,f155,f145,f167])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    spl4_12 <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    spl4_14 <=> m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | (~spl4_12 | ~spl4_14)),
% 0.21/0.52    inference(forward_demodulation,[],[f157,f147])).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl4_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f145])).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) | ~spl4_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f155])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    ~spl4_15 | spl4_5 | ~spl4_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f159,f138,f82,f161])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    spl4_5 <=> k1_xboole_0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    spl4_11 <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    k1_xboole_0 != k1_relat_1(sK2) | (spl4_5 | ~spl4_11)),
% 0.21/0.52    inference(superposition,[],[f84,f140])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl4_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f138])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) | spl4_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f82])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    spl4_14 | ~spl4_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f132,f77,f155])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    spl4_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) | ~spl4_4),
% 0.21/0.52    inference(resolution,[],[f57,f79])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f77])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    spl4_13 | ~spl4_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f143,f77,f150])).
% 0.21/0.52  fof(f143,plain,(
% 0.21/0.52    ( ! [X3] : (~r2_hidden(X3,k2_relat_1(sK2)) | ~m1_subset_1(X3,sK1)) ) | ~spl4_4),
% 0.21/0.52    inference(backward_demodulation,[],[f41,f127])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl4_4),
% 0.21/0.52    inference(resolution,[],[f56,f79])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ((! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f31,f30,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(sK0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(sK0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) & ~v1_xboole_0(X1)) => (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) & ~v1_xboole_0(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) => (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.21/0.52    inference(negated_conjecture,[],[f12])).
% 0.21/0.52  fof(f12,conjecture,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    spl4_12 | ~spl4_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f127,f77,f145])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    spl4_11 | ~spl4_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f123,f77,f138])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl4_4),
% 0.21/0.52    inference(resolution,[],[f55,f79])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    spl4_10 | ~spl4_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f109,f103,f119])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    spl4_8 <=> v1_xboole_0(k1_relat_1(k1_xboole_0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_8),
% 0.21/0.52    inference(resolution,[],[f105,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~spl4_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f103])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    spl4_8 | ~spl4_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f100,f90,f103])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    spl4_6 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~spl4_6),
% 0.21/0.52    inference(resolution,[],[f92,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k1_relat_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0) | ~spl4_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f90])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    spl4_7 | ~spl4_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f94,f77,f96])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    v1_relat_1(sK2) | ~spl4_4),
% 0.21/0.52    inference(resolution,[],[f54,f79])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    spl4_6 | ~spl4_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f88,f72,f90])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    spl4_3 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0) | ~spl4_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f87,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    ~r1_tarski(k1_xboole_0,k1_xboole_0) | v1_xboole_0(k1_xboole_0) | ~spl4_3),
% 0.21/0.52    inference(resolution,[],[f48,f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f72])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.21/0.52    inference(flattening,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    ~spl4_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f40,f82])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    spl4_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f39,f77])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    spl4_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f58,f72])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.52    inference(equality_resolution,[],[f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (21710)------------------------------
% 0.21/0.52  % (21710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (21710)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (21710)Memory used [KB]: 6268
% 0.21/0.52  % (21710)Time elapsed: 0.091 s
% 0.21/0.52  % (21710)------------------------------
% 0.21/0.52  % (21710)------------------------------
% 0.21/0.52  % (21707)Success in time 0.162 s
%------------------------------------------------------------------------------
