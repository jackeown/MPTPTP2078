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
% DateTime   : Thu Dec  3 13:06:19 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  229 ( 464 expanded)
%              Number of leaves         :   54 ( 199 expanded)
%              Depth                    :   19
%              Number of atoms          :  829 (1925 expanded)
%              Number of equality atoms :  161 ( 435 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f660,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f106,f110,f114,f129,f132,f146,f163,f173,f237,f252,f262,f305,f309,f349,f363,f368,f373,f385,f405,f414,f448,f449,f454,f519,f528,f558,f581,f583,f584,f589,f594,f603,f622,f650,f659])).

fof(f659,plain,
    ( spl11_48
    | ~ spl11_50
    | spl11_63 ),
    inference(avatar_split_clause,[],[f657,f648,f498,f451])).

fof(f451,plain,
    ( spl11_48
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_48])])).

fof(f498,plain,
    ( spl11_50
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).

fof(f648,plain,
    ( spl11_63
  <=> r2_hidden(sK10(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_63])])).

fof(f657,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl11_50
    | spl11_63 ),
    inference(resolution,[],[f651,f499])).

fof(f499,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl11_50 ),
    inference(avatar_component_clause,[],[f498])).

fof(f651,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0) )
    | spl11_63 ),
    inference(resolution,[],[f649,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK10(X1,X2),X1)
      | k1_relset_1(X1,X0,X2) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK9(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK10(X1,X2),X6),X2)
            & r2_hidden(sK10(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f46,f48,f47])).

fof(f47,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK9(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK10(X1,X2),X6),X2)
        & r2_hidden(sK10(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

fof(f649,plain,
    ( ~ r2_hidden(sK10(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | spl11_63 ),
    inference(avatar_component_clause,[],[f648])).

fof(f650,plain,
    ( ~ spl11_63
    | spl11_61 ),
    inference(avatar_split_clause,[],[f646,f620,f648])).

fof(f620,plain,
    ( spl11_61
  <=> r2_hidden(sK10(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_61])])).

fof(f646,plain,
    ( ~ r2_hidden(sK10(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | spl11_61 ),
    inference(resolution,[],[f645,f57])).

fof(f57,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f645,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(k1_xboole_0))
        | ~ r2_hidden(sK10(k1_xboole_0,k1_xboole_0),X0) )
    | spl11_61 ),
    inference(resolution,[],[f626,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f626,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_relat_1(k1_xboole_0)))
        | ~ r2_hidden(sK10(k1_xboole_0,k1_xboole_0),X1) )
    | spl11_61 ),
    inference(resolution,[],[f621,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f621,plain,
    ( ~ r2_hidden(sK10(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | spl11_61 ),
    inference(avatar_component_clause,[],[f620])).

fof(f622,plain,
    ( ~ spl11_61
    | ~ spl11_37
    | ~ spl11_59 ),
    inference(avatar_split_clause,[],[f614,f601,f347,f620])).

fof(f347,plain,
    ( spl11_37
  <=> ! [X2] :
        ( ~ r2_hidden(X2,k1_relat_1(k1_xboole_0))
        | r2_hidden(k4_tarski(X2,k1_funct_1(k1_xboole_0,X2)),k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_37])])).

fof(f601,plain,
    ( spl11_59
  <=> ! [X0] : ~ r2_hidden(k4_tarski(sK10(k1_xboole_0,k1_xboole_0),X0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_59])])).

fof(f614,plain,
    ( ~ r2_hidden(sK10(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ spl11_37
    | ~ spl11_59 ),
    inference(resolution,[],[f348,f602])).

fof(f602,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK10(k1_xboole_0,k1_xboole_0),X0),k1_xboole_0)
    | ~ spl11_59 ),
    inference(avatar_component_clause,[],[f601])).

fof(f348,plain,
    ( ! [X2] :
        ( r2_hidden(k4_tarski(X2,k1_funct_1(k1_xboole_0,X2)),k1_xboole_0)
        | ~ r2_hidden(X2,k1_relat_1(k1_xboole_0)) )
    | ~ spl11_37 ),
    inference(avatar_component_clause,[],[f347])).

fof(f603,plain,
    ( spl11_48
    | spl11_59
    | ~ spl11_50 ),
    inference(avatar_split_clause,[],[f597,f498,f601,f451])).

fof(f597,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK10(k1_xboole_0,k1_xboole_0),X0),k1_xboole_0)
        | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) )
    | ~ spl11_50 ),
    inference(resolution,[],[f499,f82])).

fof(f82,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_hidden(k4_tarski(sK10(X1,X2),X6),X2)
      | k1_relset_1(X1,X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f594,plain,
    ( ~ spl11_50
    | ~ spl11_48
    | spl11_49 ),
    inference(avatar_split_clause,[],[f591,f494,f451,f498])).

fof(f494,plain,
    ( spl11_49
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_49])])).

fof(f591,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl11_49 ),
    inference(resolution,[],[f588,f96])).

fof(f96,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f26])).

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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f588,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl11_49 ),
    inference(avatar_component_clause,[],[f494])).

fof(f589,plain,
    ( ~ spl11_49
    | ~ spl11_23
    | spl11_40 ),
    inference(avatar_split_clause,[],[f587,f366,f256,f494])).

fof(f256,plain,
    ( spl11_23
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).

fof(f366,plain,
    ( spl11_40
  <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_40])])).

fof(f587,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl11_23
    | spl11_40 ),
    inference(forward_demodulation,[],[f447,f257])).

fof(f257,plain,
    ( k1_xboole_0 = sK3
    | ~ spl11_23 ),
    inference(avatar_component_clause,[],[f256])).

fof(f447,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | spl11_40 ),
    inference(avatar_component_clause,[],[f366])).

fof(f584,plain,
    ( k1_xboole_0 != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f583,plain,(
    spl11_58 ),
    inference(avatar_contradiction_clause,[],[f582])).

fof(f582,plain,
    ( $false
    | spl11_58 ),
    inference(resolution,[],[f580,f57])).

fof(f580,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | spl11_58 ),
    inference(avatar_component_clause,[],[f579])).

fof(f579,plain,
    ( spl11_58
  <=> r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_58])])).

fof(f581,plain,
    ( ~ spl11_58
    | spl11_50 ),
    inference(avatar_split_clause,[],[f577,f498,f579])).

fof(f577,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | spl11_50 ),
    inference(resolution,[],[f515,f69])).

fof(f515,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl11_50 ),
    inference(avatar_component_clause,[],[f498])).

fof(f558,plain,
    ( ~ spl11_10
    | ~ spl11_23
    | ~ spl11_29
    | ~ spl11_52 ),
    inference(avatar_contradiction_clause,[],[f557])).

fof(f557,plain,
    ( $false
    | ~ spl11_10
    | ~ spl11_23
    | ~ spl11_29
    | ~ spl11_52 ),
    inference(subsumption_resolution,[],[f308,f556])).

fof(f556,plain,
    ( ! [X0] : ~ r2_hidden(sK4,k9_relat_1(k1_xboole_0,X0))
    | ~ spl11_10
    | ~ spl11_23
    | ~ spl11_52 ),
    inference(equality_resolution,[],[f539])).

fof(f539,plain,
    ( ! [X0,X1] :
        ( sK4 != X1
        | ~ r2_hidden(X1,k9_relat_1(k1_xboole_0,X0)) )
    | ~ spl11_10
    | ~ spl11_23
    | ~ spl11_52 ),
    inference(subsumption_resolution,[],[f482,f527])).

fof(f527,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK7(k1_xboole_0,X0,X1),k1_xboole_0)
        | ~ r2_hidden(X1,k9_relat_1(k1_xboole_0,X0)) )
    | ~ spl11_52 ),
    inference(avatar_component_clause,[],[f526])).

fof(f526,plain,
    ( spl11_52
  <=> ! [X1,X0] :
        ( r2_hidden(sK7(k1_xboole_0,X0,X1),k1_xboole_0)
        | ~ r2_hidden(X1,k9_relat_1(k1_xboole_0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).

fof(f482,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK7(k1_xboole_0,X0,X1),k1_xboole_0)
        | ~ r2_hidden(X1,k9_relat_1(k1_xboole_0,X0))
        | sK4 != X1 )
    | ~ spl11_10
    | ~ spl11_23 ),
    inference(superposition,[],[f200,f257])).

fof(f200,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK7(sK3,X1,X0),k1_xboole_0)
        | ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | sK4 != X0 )
    | ~ spl11_10 ),
    inference(duplicate_literal_removal,[],[f199])).

fof(f199,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | ~ r2_hidden(sK7(sK3,X1,X0),k1_xboole_0)
        | ~ r2_hidden(sK7(sK3,X1,X0),k1_xboole_0)
        | sK4 != X0 )
    | ~ spl11_10 ),
    inference(resolution,[],[f198,f57])).

fof(f198,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X2,sK0)
        | ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | ~ r2_hidden(sK7(sK3,X1,X0),X2)
        | ~ r2_hidden(sK7(sK3,X1,X0),k1_xboole_0)
        | sK4 != X0 )
    | ~ spl11_10 ),
    inference(resolution,[],[f189,f69])).

fof(f189,plain,
    ( ! [X2,X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
        | sK4 != X2
        | ~ r2_hidden(X2,k9_relat_1(sK3,X1))
        | ~ r2_hidden(sK7(sK3,X1,X2),X3)
        | ~ r2_hidden(sK7(sK3,X1,X2),k1_xboole_0) )
    | ~ spl11_10 ),
    inference(resolution,[],[f187,f68])).

fof(f187,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK7(sK3,X1,X0),sK0)
        | ~ r2_hidden(sK7(sK3,X1,X0),k1_xboole_0)
        | sK4 != X0
        | ~ r2_hidden(X0,k9_relat_1(sK3,X1)) )
    | ~ spl11_10 ),
    inference(resolution,[],[f186,f57])).

fof(f186,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X2,sK2)
        | ~ r2_hidden(X1,k9_relat_1(sK3,X0))
        | ~ r2_hidden(sK7(sK3,X0,X1),X2)
        | sK4 != X1
        | ~ r2_hidden(sK7(sK3,X0,X1),sK0) )
    | ~ spl11_10 ),
    inference(resolution,[],[f167,f69])).

fof(f167,plain,
    ( ! [X2,X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(sK2))
        | ~ r2_hidden(sK7(sK3,X2,X1),sK0)
        | ~ r2_hidden(X1,k9_relat_1(sK3,X2))
        | ~ r2_hidden(sK7(sK3,X2,X1),X3)
        | sK4 != X1 )
    | ~ spl11_10 ),
    inference(resolution,[],[f165,f68])).

fof(f165,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(sK7(sK3,X2,X3),sK2)
        | sK4 != X3
        | ~ r2_hidden(sK7(sK3,X2,X3),sK0)
        | ~ r2_hidden(X3,k9_relat_1(sK3,X2)) )
    | ~ spl11_10 ),
    inference(superposition,[],[f56,f162])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK3,sK7(sK3,X1,X0)) = X0
        | ~ r2_hidden(X0,k9_relat_1(sK3,X1)) )
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl11_10
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | k1_funct_1(sK3,sK7(sK3,X1,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f56,plain,(
    ! [X5] :
      ( k1_funct_1(sK3,X5) != sK4
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ! [X5] :
        ( k1_funct_1(sK3,X5) != sK4
        | ~ r2_hidden(X5,sK2)
        | ~ r2_hidden(X5,sK0) )
    & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f32,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK3,X5) != X4
              | ~ r2_hidden(X5,sK2)
              | ~ r2_hidden(X5,sK0) )
          & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X4] :
        ( ! [X5] :
            ( k1_funct_1(sK3,X5) != X4
            | ~ r2_hidden(X5,sK2)
            | ~ r2_hidden(X5,sK0) )
        & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
   => ( ! [X5] :
          ( k1_funct_1(sK3,X5) != sK4
          | ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(X5,sK0) )
      & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

fof(f308,plain,
    ( r2_hidden(sK4,k9_relat_1(k1_xboole_0,sK2))
    | ~ spl11_29 ),
    inference(avatar_component_clause,[],[f307])).

fof(f307,plain,
    ( spl11_29
  <=> r2_hidden(sK4,k9_relat_1(k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_29])])).

fof(f528,plain,
    ( ~ spl11_35
    | ~ spl11_28
    | spl11_52
    | ~ spl11_51 ),
    inference(avatar_split_clause,[],[f521,f513,f526,f303,f340])).

fof(f340,plain,
    ( spl11_35
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_35])])).

fof(f303,plain,
    ( spl11_28
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).

fof(f513,plain,
    ( spl11_51
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_51])])).

fof(f521,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK7(k1_xboole_0,X0,X1),k1_xboole_0)
        | ~ r2_hidden(X1,k9_relat_1(k1_xboole_0,X0))
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl11_51 ),
    inference(superposition,[],[f92,f514])).

fof(f514,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl11_51 ),
    inference(avatar_component_clause,[],[f513])).

fof(f92,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK5(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK5(X0,X1,X2),X2) )
              & ( ( sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2))
                  & r2_hidden(sK6(X0,X1,X2),X1)
                  & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
                    & r2_hidden(sK7(X0,X1,X6),X1)
                    & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f35,f38,f37,f36])).

fof(f36,plain,(
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
              ( k1_funct_1(X0,X4) != sK5(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK5(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = sK5(X0,X1,X2)
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2))
        & r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
        & r2_hidden(sK7(X0,X1,X6),X1)
        & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(f519,plain,
    ( spl11_51
    | ~ spl11_50
    | ~ spl11_23
    | ~ spl11_47 ),
    inference(avatar_split_clause,[],[f518,f445,f256,f498,f513])).

fof(f445,plain,
    ( spl11_47
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_47])])).

fof(f518,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl11_23
    | ~ spl11_47 ),
    inference(forward_demodulation,[],[f517,f257])).

fof(f517,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl11_23
    | ~ spl11_47 ),
    inference(forward_demodulation,[],[f509,f257])).

fof(f509,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl11_47 ),
    inference(superposition,[],[f74,f446])).

fof(f446,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl11_47 ),
    inference(avatar_component_clause,[],[f445])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f454,plain,
    ( spl11_21
    | ~ spl11_2
    | ~ spl11_19 ),
    inference(avatar_split_clause,[],[f239,f234,f104,f246])).

fof(f246,plain,
    ( spl11_21
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f104,plain,
    ( spl11_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f234,plain,
    ( spl11_19
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f239,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl11_2
    | ~ spl11_19 ),
    inference(superposition,[],[f105,f235])).

fof(f235,plain,
    ( k1_xboole_0 = sK1
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f234])).

fof(f105,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f449,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | k1_xboole_0 != sK0
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f448,plain,
    ( spl11_47
    | ~ spl11_40
    | ~ spl11_41 ),
    inference(avatar_split_clause,[],[f441,f371,f366,f445])).

fof(f371,plain,
    ( spl11_41
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_41])])).

fof(f441,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl11_41 ),
    inference(resolution,[],[f372,f97])).

fof(f97,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f372,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl11_41 ),
    inference(avatar_component_clause,[],[f371])).

fof(f414,plain,
    ( ~ spl11_8
    | ~ spl11_11
    | ~ spl11_42 ),
    inference(avatar_split_clause,[],[f412,f383,f171,f144])).

fof(f144,plain,
    ( spl11_8
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f171,plain,
    ( spl11_11
  <=> ! [X0] :
        ( sK4 != X0
        | ~ r2_hidden(X0,k9_relat_1(sK3,sK2))
        | ~ r2_hidden(sK7(sK3,sK2,X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f383,plain,
    ( spl11_42
  <=> ! [X1,X0] :
        ( r2_hidden(sK7(sK3,X0,X1),sK0)
        | ~ r2_hidden(X1,k9_relat_1(sK3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_42])])).

fof(f412,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl11_11
    | ~ spl11_42 ),
    inference(equality_resolution,[],[f398])).

fof(f398,plain,
    ( ! [X0] :
        ( sK4 != X0
        | ~ r2_hidden(X0,k9_relat_1(sK3,sK2)) )
    | ~ spl11_11
    | ~ spl11_42 ),
    inference(subsumption_resolution,[],[f172,f384])).

fof(f384,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK7(sK3,X0,X1),sK0)
        | ~ r2_hidden(X1,k9_relat_1(sK3,X0)) )
    | ~ spl11_42 ),
    inference(avatar_component_clause,[],[f383])).

fof(f172,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK7(sK3,sK2,X0),sK0)
        | ~ r2_hidden(X0,k9_relat_1(sK3,sK2))
        | sK4 != X0 )
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f171])).

fof(f405,plain,(
    spl11_35 ),
    inference(avatar_contradiction_clause,[],[f404])).

fof(f404,plain,
    ( $false
    | spl11_35 ),
    inference(subsumption_resolution,[],[f67,f402])).

fof(f402,plain,
    ( ! [X0] : ~ v1_relat_1(X0)
    | spl11_35 ),
    inference(resolution,[],[f401,f57])).

fof(f401,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | ~ v1_relat_1(X0) )
    | spl11_35 ),
    inference(resolution,[],[f354,f69])).

fof(f354,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl11_35 ),
    inference(resolution,[],[f341,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f341,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl11_35 ),
    inference(avatar_component_clause,[],[f340])).

fof(f67,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f385,plain,
    ( ~ spl11_5
    | ~ spl11_4
    | spl11_42
    | ~ spl11_39 ),
    inference(avatar_split_clause,[],[f379,f360,f383,f112,f117])).

fof(f117,plain,
    ( spl11_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f112,plain,
    ( spl11_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f360,plain,
    ( spl11_39
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_39])])).

fof(f379,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK7(sK3,X0,X1),sK0)
        | ~ r2_hidden(X1,k9_relat_1(sK3,X0))
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl11_39 ),
    inference(superposition,[],[f92,f361])).

fof(f361,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl11_39 ),
    inference(avatar_component_clause,[],[f360])).

fof(f373,plain,
    ( spl11_41
    | ~ spl11_21
    | ~ spl11_24 ),
    inference(avatar_split_clause,[],[f369,f259,f246,f371])).

fof(f259,plain,
    ( spl11_24
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f369,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl11_21
    | ~ spl11_24 ),
    inference(forward_demodulation,[],[f247,f260])).

fof(f260,plain,
    ( k1_xboole_0 = sK0
    | ~ spl11_24 ),
    inference(avatar_component_clause,[],[f259])).

fof(f247,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl11_21 ),
    inference(avatar_component_clause,[],[f246])).

fof(f368,plain,
    ( spl11_40
    | ~ spl11_22
    | ~ spl11_24 ),
    inference(avatar_split_clause,[],[f364,f259,f250,f366])).

fof(f250,plain,
    ( spl11_22
  <=> v1_funct_2(sK3,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f364,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl11_22
    | ~ spl11_24 ),
    inference(forward_demodulation,[],[f251,f260])).

fof(f251,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f250])).

fof(f363,plain,
    ( ~ spl11_2
    | spl11_39
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f358,f231,f360,f104])).

fof(f231,plain,
    ( spl11_18
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f358,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl11_18 ),
    inference(superposition,[],[f74,f232])).

fof(f232,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f231])).

fof(f349,plain,
    ( ~ spl11_35
    | spl11_37
    | ~ spl11_28 ),
    inference(avatar_split_clause,[],[f337,f303,f347,f340])).

fof(f337,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_relat_1(k1_xboole_0))
        | r2_hidden(k4_tarski(X2,k1_funct_1(k1_xboole_0,X2)),k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl11_28 ),
    inference(resolution,[],[f304,f98])).

fof(f98,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f304,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl11_28 ),
    inference(avatar_component_clause,[],[f303])).

fof(f309,plain,
    ( spl11_29
    | ~ spl11_8
    | ~ spl11_23 ),
    inference(avatar_split_clause,[],[f271,f256,f144,f307])).

fof(f271,plain,
    ( r2_hidden(sK4,k9_relat_1(k1_xboole_0,sK2))
    | ~ spl11_8
    | ~ spl11_23 ),
    inference(superposition,[],[f145,f257])).

fof(f145,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f144])).

fof(f305,plain,
    ( spl11_28
    | ~ spl11_4
    | ~ spl11_23 ),
    inference(avatar_split_clause,[],[f267,f256,f112,f303])).

fof(f267,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl11_4
    | ~ spl11_23 ),
    inference(superposition,[],[f113,f257])).

fof(f113,plain,
    ( v1_funct_1(sK3)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f262,plain,
    ( spl11_23
    | spl11_24
    | ~ spl11_22
    | ~ spl11_21 ),
    inference(avatar_split_clause,[],[f253,f246,f250,f259,f256])).

fof(f253,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ spl11_21 ),
    inference(resolution,[],[f247,f95])).

fof(f95,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f252,plain,
    ( spl11_22
    | ~ spl11_3
    | ~ spl11_19 ),
    inference(avatar_split_clause,[],[f240,f234,f108,f250])).

fof(f108,plain,
    ( spl11_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f240,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl11_3
    | ~ spl11_19 ),
    inference(superposition,[],[f109,f235])).

fof(f109,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f237,plain,
    ( spl11_18
    | spl11_19
    | ~ spl11_3
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f228,f104,f108,f234,f231])).

fof(f228,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl11_2 ),
    inference(resolution,[],[f75,f105])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f173,plain,
    ( ~ spl11_5
    | ~ spl11_4
    | spl11_11
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f168,f161,f171,f112,f117])).

fof(f168,plain,
    ( ! [X0] :
        ( sK4 != X0
        | ~ r2_hidden(sK7(sK3,sK2,X0),sK0)
        | ~ r2_hidden(X0,k9_relat_1(sK3,sK2))
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl11_10 ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,
    ( ! [X0] :
        ( sK4 != X0
        | ~ r2_hidden(sK7(sK3,sK2,X0),sK0)
        | ~ r2_hidden(X0,k9_relat_1(sK3,sK2))
        | ~ r2_hidden(X0,k9_relat_1(sK3,sK2))
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl11_10 ),
    inference(resolution,[],[f165,f91])).

fof(f91,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f163,plain,
    ( ~ spl11_5
    | spl11_10
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f159,f112,f161,f117])).

fof(f159,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | k1_funct_1(sK3,sK7(sK3,X1,X0)) = X0
        | ~ v1_relat_1(sK3) )
    | ~ spl11_4 ),
    inference(resolution,[],[f90,f113])).

fof(f90,plain,(
    ! [X6,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | k1_funct_1(X0,sK7(X0,X1,X6)) = X6
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f146,plain,
    ( ~ spl11_2
    | spl11_8
    | ~ spl11_1 ),
    inference(avatar_split_clause,[],[f141,f100,f144,f104])).

fof(f100,plain,
    ( spl11_1
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f141,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl11_1 ),
    inference(superposition,[],[f101,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f101,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f132,plain,(
    spl11_7 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl11_7 ),
    inference(resolution,[],[f128,f67])).

fof(f128,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl11_7 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl11_7
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f129,plain,
    ( ~ spl11_7
    | ~ spl11_2
    | spl11_5 ),
    inference(avatar_split_clause,[],[f124,f117,f104,f127])).

fof(f124,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl11_2
    | spl11_5 ),
    inference(resolution,[],[f123,f105])).

fof(f123,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl11_5 ),
    inference(resolution,[],[f118,f58])).

fof(f118,plain,
    ( ~ v1_relat_1(sK3)
    | spl11_5 ),
    inference(avatar_component_clause,[],[f117])).

fof(f114,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f52,f112])).

fof(f52,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f110,plain,(
    spl11_3 ),
    inference(avatar_split_clause,[],[f53,f108])).

fof(f53,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f106,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f54,f104])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f102,plain,(
    spl11_1 ),
    inference(avatar_split_clause,[],[f55,f100])).

fof(f55,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:45:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (9409)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.46  % (9414)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (9416)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (9410)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (9417)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (9423)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (9422)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (9418)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.50  % (9411)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (9421)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (9427)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.50  % (9413)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (9429)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.51  % (9412)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (9426)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.51  % (9420)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.51  % (9419)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.51  % (9425)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.51  % (9420)Refutation not found, incomplete strategy% (9420)------------------------------
% 0.20/0.51  % (9420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (9420)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (9420)Memory used [KB]: 10746
% 0.20/0.51  % (9420)Time elapsed: 0.104 s
% 0.20/0.51  % (9420)------------------------------
% 0.20/0.51  % (9420)------------------------------
% 1.26/0.51  % (9428)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.26/0.53  % (9415)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 1.26/0.53  % (9424)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.41/0.54  % (9415)Refutation found. Thanks to Tanya!
% 1.41/0.54  % SZS status Theorem for theBenchmark
% 1.41/0.54  % SZS output start Proof for theBenchmark
% 1.41/0.54  fof(f660,plain,(
% 1.41/0.54    $false),
% 1.41/0.54    inference(avatar_sat_refutation,[],[f102,f106,f110,f114,f129,f132,f146,f163,f173,f237,f252,f262,f305,f309,f349,f363,f368,f373,f385,f405,f414,f448,f449,f454,f519,f528,f558,f581,f583,f584,f589,f594,f603,f622,f650,f659])).
% 1.41/0.54  fof(f659,plain,(
% 1.41/0.54    spl11_48 | ~spl11_50 | spl11_63),
% 1.41/0.54    inference(avatar_split_clause,[],[f657,f648,f498,f451])).
% 1.41/0.54  fof(f451,plain,(
% 1.41/0.54    spl11_48 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_48])])).
% 1.41/0.54  fof(f498,plain,(
% 1.41/0.54    spl11_50 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).
% 1.41/0.54  fof(f648,plain,(
% 1.41/0.54    spl11_63 <=> r2_hidden(sK10(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_63])])).
% 1.41/0.54  fof(f657,plain,(
% 1.41/0.54    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl11_50 | spl11_63)),
% 1.41/0.54    inference(resolution,[],[f651,f499])).
% 1.41/0.54  fof(f499,plain,(
% 1.41/0.54    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl11_50),
% 1.41/0.54    inference(avatar_component_clause,[],[f498])).
% 1.41/0.54  fof(f651,plain,(
% 1.41/0.54    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)) ) | spl11_63),
% 1.41/0.54    inference(resolution,[],[f649,f81])).
% 1.41/0.55  fof(f81,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK10(X1,X2),X1) | k1_relset_1(X1,X0,X2) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 1.41/0.55    inference(cnf_transformation,[],[f49])).
% 1.41/0.55  fof(f49,plain,(
% 1.41/0.55    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK9(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK10(X1,X2),X6),X2) & r2_hidden(sK10(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.41/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f46,f48,f47])).
% 1.41/0.55  fof(f47,plain,(
% 1.41/0.55    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK9(X2,X3)),X2))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f48,plain,(
% 1.41/0.55    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK10(X1,X2),X6),X2) & r2_hidden(sK10(X1,X2),X1)))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f46,plain,(
% 1.41/0.55    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.41/0.55    inference(rectify,[],[f45])).
% 1.41/0.55  fof(f45,plain,(
% 1.41/0.55    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.41/0.55    inference(nnf_transformation,[],[f27])).
% 1.41/0.55  fof(f27,plain,(
% 1.41/0.55    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.41/0.55    inference(ennf_transformation,[],[f11])).
% 1.41/0.55  fof(f11,axiom,(
% 1.41/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).
% 1.41/0.55  fof(f649,plain,(
% 1.41/0.55    ~r2_hidden(sK10(k1_xboole_0,k1_xboole_0),k1_xboole_0) | spl11_63),
% 1.41/0.55    inference(avatar_component_clause,[],[f648])).
% 1.41/0.55  fof(f650,plain,(
% 1.41/0.55    ~spl11_63 | spl11_61),
% 1.41/0.55    inference(avatar_split_clause,[],[f646,f620,f648])).
% 1.41/0.55  fof(f620,plain,(
% 1.41/0.55    spl11_61 <=> r2_hidden(sK10(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_61])])).
% 1.41/0.55  fof(f646,plain,(
% 1.41/0.55    ~r2_hidden(sK10(k1_xboole_0,k1_xboole_0),k1_xboole_0) | spl11_61),
% 1.41/0.55    inference(resolution,[],[f645,f57])).
% 1.41/0.55  fof(f57,plain,(
% 1.41/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f1])).
% 1.41/0.55  fof(f1,axiom,(
% 1.41/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.41/0.55  fof(f645,plain,(
% 1.41/0.55    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(k1_xboole_0)) | ~r2_hidden(sK10(k1_xboole_0,k1_xboole_0),X0)) ) | spl11_61),
% 1.41/0.55    inference(resolution,[],[f626,f69])).
% 1.41/0.55  fof(f69,plain,(
% 1.41/0.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f22])).
% 1.41/0.55  fof(f22,plain,(
% 1.41/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 1.41/0.55    inference(ennf_transformation,[],[f15])).
% 1.41/0.55  fof(f15,plain,(
% 1.41/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 1.41/0.55    inference(unused_predicate_definition_removal,[],[f3])).
% 1.41/0.55  fof(f3,axiom,(
% 1.41/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.41/0.55  fof(f626,plain,(
% 1.41/0.55    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_relat_1(k1_xboole_0))) | ~r2_hidden(sK10(k1_xboole_0,k1_xboole_0),X1)) ) | spl11_61),
% 1.41/0.55    inference(resolution,[],[f621,f68])).
% 1.41/0.55  fof(f68,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.41/0.55    inference(cnf_transformation,[],[f21])).
% 1.41/0.55  fof(f21,plain,(
% 1.41/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.41/0.55    inference(ennf_transformation,[],[f2])).
% 1.41/0.55  fof(f2,axiom,(
% 1.41/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.41/0.55  fof(f621,plain,(
% 1.41/0.55    ~r2_hidden(sK10(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | spl11_61),
% 1.41/0.55    inference(avatar_component_clause,[],[f620])).
% 1.41/0.55  fof(f622,plain,(
% 1.41/0.55    ~spl11_61 | ~spl11_37 | ~spl11_59),
% 1.41/0.55    inference(avatar_split_clause,[],[f614,f601,f347,f620])).
% 1.41/0.55  fof(f347,plain,(
% 1.41/0.55    spl11_37 <=> ! [X2] : (~r2_hidden(X2,k1_relat_1(k1_xboole_0)) | r2_hidden(k4_tarski(X2,k1_funct_1(k1_xboole_0,X2)),k1_xboole_0))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_37])])).
% 1.41/0.55  fof(f601,plain,(
% 1.41/0.55    spl11_59 <=> ! [X0] : ~r2_hidden(k4_tarski(sK10(k1_xboole_0,k1_xboole_0),X0),k1_xboole_0)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_59])])).
% 1.41/0.55  fof(f614,plain,(
% 1.41/0.55    ~r2_hidden(sK10(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | (~spl11_37 | ~spl11_59)),
% 1.41/0.55    inference(resolution,[],[f348,f602])).
% 1.41/0.55  fof(f602,plain,(
% 1.41/0.55    ( ! [X0] : (~r2_hidden(k4_tarski(sK10(k1_xboole_0,k1_xboole_0),X0),k1_xboole_0)) ) | ~spl11_59),
% 1.41/0.55    inference(avatar_component_clause,[],[f601])).
% 1.41/0.55  fof(f348,plain,(
% 1.41/0.55    ( ! [X2] : (r2_hidden(k4_tarski(X2,k1_funct_1(k1_xboole_0,X2)),k1_xboole_0) | ~r2_hidden(X2,k1_relat_1(k1_xboole_0))) ) | ~spl11_37),
% 1.41/0.55    inference(avatar_component_clause,[],[f347])).
% 1.41/0.55  fof(f603,plain,(
% 1.41/0.55    spl11_48 | spl11_59 | ~spl11_50),
% 1.41/0.55    inference(avatar_split_clause,[],[f597,f498,f601,f451])).
% 1.41/0.55  fof(f597,plain,(
% 1.41/0.55    ( ! [X0] : (~r2_hidden(k4_tarski(sK10(k1_xboole_0,k1_xboole_0),X0),k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ) | ~spl11_50),
% 1.41/0.55    inference(resolution,[],[f499,f82])).
% 1.41/0.55  fof(f82,plain,(
% 1.41/0.55    ( ! [X6,X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_hidden(k4_tarski(sK10(X1,X2),X6),X2) | k1_relset_1(X1,X0,X2) = X1) )),
% 1.41/0.55    inference(cnf_transformation,[],[f49])).
% 1.41/0.55  fof(f594,plain,(
% 1.41/0.55    ~spl11_50 | ~spl11_48 | spl11_49),
% 1.41/0.55    inference(avatar_split_clause,[],[f591,f494,f451,f498])).
% 1.41/0.55  fof(f494,plain,(
% 1.41/0.55    spl11_49 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_49])])).
% 1.41/0.55  fof(f591,plain,(
% 1.41/0.55    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | spl11_49),
% 1.41/0.55    inference(resolution,[],[f588,f96])).
% 1.41/0.55  fof(f96,plain,(
% 1.41/0.55    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.41/0.55    inference(equality_resolution,[],[f78])).
% 1.41/0.55  fof(f78,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.55    inference(cnf_transformation,[],[f44])).
% 1.41/0.55  fof(f44,plain,(
% 1.41/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.55    inference(nnf_transformation,[],[f26])).
% 1.41/0.55  fof(f26,plain,(
% 1.41/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.55    inference(flattening,[],[f25])).
% 1.41/0.55  fof(f25,plain,(
% 1.41/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.55    inference(ennf_transformation,[],[f12])).
% 1.41/0.55  fof(f12,axiom,(
% 1.41/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.41/0.55  fof(f588,plain,(
% 1.41/0.55    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | spl11_49),
% 1.41/0.55    inference(avatar_component_clause,[],[f494])).
% 1.41/0.55  fof(f589,plain,(
% 1.41/0.55    ~spl11_49 | ~spl11_23 | spl11_40),
% 1.41/0.55    inference(avatar_split_clause,[],[f587,f366,f256,f494])).
% 1.41/0.55  fof(f256,plain,(
% 1.41/0.55    spl11_23 <=> k1_xboole_0 = sK3),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).
% 1.41/0.55  fof(f366,plain,(
% 1.41/0.55    spl11_40 <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_40])])).
% 1.41/0.55  fof(f587,plain,(
% 1.41/0.55    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl11_23 | spl11_40)),
% 1.41/0.55    inference(forward_demodulation,[],[f447,f257])).
% 1.41/0.55  fof(f257,plain,(
% 1.41/0.55    k1_xboole_0 = sK3 | ~spl11_23),
% 1.41/0.55    inference(avatar_component_clause,[],[f256])).
% 1.41/0.55  fof(f447,plain,(
% 1.41/0.55    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | spl11_40),
% 1.41/0.55    inference(avatar_component_clause,[],[f366])).
% 1.41/0.55  fof(f584,plain,(
% 1.41/0.55    k1_xboole_0 != sK3 | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.41/0.55    introduced(theory_tautology_sat_conflict,[])).
% 1.41/0.55  fof(f583,plain,(
% 1.41/0.55    spl11_58),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f582])).
% 1.41/0.55  fof(f582,plain,(
% 1.41/0.55    $false | spl11_58),
% 1.41/0.55    inference(resolution,[],[f580,f57])).
% 1.41/0.55  fof(f580,plain,(
% 1.41/0.55    ~r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | spl11_58),
% 1.41/0.55    inference(avatar_component_clause,[],[f579])).
% 1.41/0.55  fof(f579,plain,(
% 1.41/0.55    spl11_58 <=> r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_58])])).
% 1.41/0.55  fof(f581,plain,(
% 1.41/0.55    ~spl11_58 | spl11_50),
% 1.41/0.55    inference(avatar_split_clause,[],[f577,f498,f579])).
% 1.41/0.55  fof(f577,plain,(
% 1.41/0.55    ~r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | spl11_50),
% 1.41/0.55    inference(resolution,[],[f515,f69])).
% 1.41/0.55  fof(f515,plain,(
% 1.41/0.55    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | spl11_50),
% 1.41/0.55    inference(avatar_component_clause,[],[f498])).
% 1.41/0.55  fof(f558,plain,(
% 1.41/0.55    ~spl11_10 | ~spl11_23 | ~spl11_29 | ~spl11_52),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f557])).
% 1.41/0.55  fof(f557,plain,(
% 1.41/0.55    $false | (~spl11_10 | ~spl11_23 | ~spl11_29 | ~spl11_52)),
% 1.41/0.55    inference(subsumption_resolution,[],[f308,f556])).
% 1.41/0.55  fof(f556,plain,(
% 1.41/0.55    ( ! [X0] : (~r2_hidden(sK4,k9_relat_1(k1_xboole_0,X0))) ) | (~spl11_10 | ~spl11_23 | ~spl11_52)),
% 1.41/0.55    inference(equality_resolution,[],[f539])).
% 1.41/0.55  fof(f539,plain,(
% 1.41/0.55    ( ! [X0,X1] : (sK4 != X1 | ~r2_hidden(X1,k9_relat_1(k1_xboole_0,X0))) ) | (~spl11_10 | ~spl11_23 | ~spl11_52)),
% 1.41/0.55    inference(subsumption_resolution,[],[f482,f527])).
% 1.41/0.55  fof(f527,plain,(
% 1.41/0.55    ( ! [X0,X1] : (r2_hidden(sK7(k1_xboole_0,X0,X1),k1_xboole_0) | ~r2_hidden(X1,k9_relat_1(k1_xboole_0,X0))) ) | ~spl11_52),
% 1.41/0.55    inference(avatar_component_clause,[],[f526])).
% 1.41/0.55  fof(f526,plain,(
% 1.41/0.55    spl11_52 <=> ! [X1,X0] : (r2_hidden(sK7(k1_xboole_0,X0,X1),k1_xboole_0) | ~r2_hidden(X1,k9_relat_1(k1_xboole_0,X0)))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).
% 1.41/0.55  fof(f482,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~r2_hidden(sK7(k1_xboole_0,X0,X1),k1_xboole_0) | ~r2_hidden(X1,k9_relat_1(k1_xboole_0,X0)) | sK4 != X1) ) | (~spl11_10 | ~spl11_23)),
% 1.41/0.55    inference(superposition,[],[f200,f257])).
% 1.41/0.55  fof(f200,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~r2_hidden(sK7(sK3,X1,X0),k1_xboole_0) | ~r2_hidden(X0,k9_relat_1(sK3,X1)) | sK4 != X0) ) | ~spl11_10),
% 1.41/0.55    inference(duplicate_literal_removal,[],[f199])).
% 1.41/0.55  fof(f199,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | ~r2_hidden(sK7(sK3,X1,X0),k1_xboole_0) | ~r2_hidden(sK7(sK3,X1,X0),k1_xboole_0) | sK4 != X0) ) | ~spl11_10),
% 1.41/0.55    inference(resolution,[],[f198,f57])).
% 1.41/0.55  fof(f198,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X2,sK0) | ~r2_hidden(X0,k9_relat_1(sK3,X1)) | ~r2_hidden(sK7(sK3,X1,X0),X2) | ~r2_hidden(sK7(sK3,X1,X0),k1_xboole_0) | sK4 != X0) ) | ~spl11_10),
% 1.41/0.55    inference(resolution,[],[f189,f69])).
% 1.41/0.55  fof(f189,plain,(
% 1.41/0.55    ( ! [X2,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(sK0)) | sK4 != X2 | ~r2_hidden(X2,k9_relat_1(sK3,X1)) | ~r2_hidden(sK7(sK3,X1,X2),X3) | ~r2_hidden(sK7(sK3,X1,X2),k1_xboole_0)) ) | ~spl11_10),
% 1.41/0.55    inference(resolution,[],[f187,f68])).
% 1.41/0.55  fof(f187,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~r2_hidden(sK7(sK3,X1,X0),sK0) | ~r2_hidden(sK7(sK3,X1,X0),k1_xboole_0) | sK4 != X0 | ~r2_hidden(X0,k9_relat_1(sK3,X1))) ) | ~spl11_10),
% 1.41/0.55    inference(resolution,[],[f186,f57])).
% 1.41/0.55  fof(f186,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X2,sK2) | ~r2_hidden(X1,k9_relat_1(sK3,X0)) | ~r2_hidden(sK7(sK3,X0,X1),X2) | sK4 != X1 | ~r2_hidden(sK7(sK3,X0,X1),sK0)) ) | ~spl11_10),
% 1.41/0.55    inference(resolution,[],[f167,f69])).
% 1.41/0.55  fof(f167,plain,(
% 1.41/0.55    ( ! [X2,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(sK2)) | ~r2_hidden(sK7(sK3,X2,X1),sK0) | ~r2_hidden(X1,k9_relat_1(sK3,X2)) | ~r2_hidden(sK7(sK3,X2,X1),X3) | sK4 != X1) ) | ~spl11_10),
% 1.41/0.55    inference(resolution,[],[f165,f68])).
% 1.41/0.55  fof(f165,plain,(
% 1.41/0.55    ( ! [X2,X3] : (~r2_hidden(sK7(sK3,X2,X3),sK2) | sK4 != X3 | ~r2_hidden(sK7(sK3,X2,X3),sK0) | ~r2_hidden(X3,k9_relat_1(sK3,X2))) ) | ~spl11_10),
% 1.41/0.55    inference(superposition,[],[f56,f162])).
% 1.41/0.55  fof(f162,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k1_funct_1(sK3,sK7(sK3,X1,X0)) = X0 | ~r2_hidden(X0,k9_relat_1(sK3,X1))) ) | ~spl11_10),
% 1.41/0.55    inference(avatar_component_clause,[],[f161])).
% 1.41/0.55  fof(f161,plain,(
% 1.41/0.55    spl11_10 <=> ! [X1,X0] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | k1_funct_1(sK3,sK7(sK3,X1,X0)) = X0)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 1.41/0.55  fof(f56,plain,(
% 1.41/0.55    ( ! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f33])).
% 1.41/0.55  fof(f33,plain,(
% 1.41/0.55    (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.41/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f32,f31])).
% 1.41/0.55  fof(f31,plain,(
% 1.41/0.55    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f32,plain,(
% 1.41/0.55    ? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) => (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f17,plain,(
% 1.41/0.55    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.41/0.55    inference(flattening,[],[f16])).
% 1.41/0.55  fof(f16,plain,(
% 1.41/0.55    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.41/0.55    inference(ennf_transformation,[],[f14])).
% 1.41/0.55  fof(f14,negated_conjecture,(
% 1.41/0.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.41/0.55    inference(negated_conjecture,[],[f13])).
% 1.41/0.55  fof(f13,conjecture,(
% 1.41/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).
% 1.41/0.55  fof(f308,plain,(
% 1.41/0.55    r2_hidden(sK4,k9_relat_1(k1_xboole_0,sK2)) | ~spl11_29),
% 1.41/0.55    inference(avatar_component_clause,[],[f307])).
% 1.41/0.55  fof(f307,plain,(
% 1.41/0.55    spl11_29 <=> r2_hidden(sK4,k9_relat_1(k1_xboole_0,sK2))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_29])])).
% 1.41/0.55  fof(f528,plain,(
% 1.41/0.55    ~spl11_35 | ~spl11_28 | spl11_52 | ~spl11_51),
% 1.41/0.55    inference(avatar_split_clause,[],[f521,f513,f526,f303,f340])).
% 1.41/0.55  fof(f340,plain,(
% 1.41/0.55    spl11_35 <=> v1_relat_1(k1_xboole_0)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_35])])).
% 1.41/0.55  fof(f303,plain,(
% 1.41/0.55    spl11_28 <=> v1_funct_1(k1_xboole_0)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).
% 1.41/0.55  fof(f513,plain,(
% 1.41/0.55    spl11_51 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_51])])).
% 1.41/0.55  fof(f521,plain,(
% 1.41/0.55    ( ! [X0,X1] : (r2_hidden(sK7(k1_xboole_0,X0,X1),k1_xboole_0) | ~r2_hidden(X1,k9_relat_1(k1_xboole_0,X0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl11_51),
% 1.41/0.55    inference(superposition,[],[f92,f514])).
% 1.41/0.55  fof(f514,plain,(
% 1.41/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl11_51),
% 1.41/0.55    inference(avatar_component_clause,[],[f513])).
% 1.41/0.55  fof(f92,plain,(
% 1.41/0.55    ( ! [X6,X0,X1] : (r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.55    inference(equality_resolution,[],[f59])).
% 1.41/0.55  fof(f59,plain,(
% 1.41/0.55    ( ! [X6,X2,X0,X1] : (r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f39])).
% 1.41/0.55  fof(f39,plain,(
% 1.41/0.55    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK5(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK7(X0,X1,X6)) = X6 & r2_hidden(sK7(X0,X1,X6),X1) & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.41/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f35,f38,f37,f36])).
% 1.41/0.55  fof(f36,plain,(
% 1.41/0.55    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK5(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK5(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f37,plain,(
% 1.41/0.55    ! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = sK5(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f38,plain,(
% 1.41/0.55    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK7(X0,X1,X6)) = X6 & r2_hidden(sK7(X0,X1,X6),X1) & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f35,plain,(
% 1.41/0.55    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.41/0.55    inference(rectify,[],[f34])).
% 1.41/0.55  fof(f34,plain,(
% 1.41/0.55    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.41/0.55    inference(nnf_transformation,[],[f20])).
% 1.41/0.55  fof(f20,plain,(
% 1.41/0.55    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.41/0.55    inference(flattening,[],[f19])).
% 1.41/0.55  fof(f19,plain,(
% 1.41/0.55    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.41/0.55    inference(ennf_transformation,[],[f7])).
% 1.41/0.55  fof(f7,axiom,(
% 1.41/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).
% 1.41/0.55  fof(f519,plain,(
% 1.41/0.55    spl11_51 | ~spl11_50 | ~spl11_23 | ~spl11_47),
% 1.41/0.55    inference(avatar_split_clause,[],[f518,f445,f256,f498,f513])).
% 1.41/0.55  fof(f445,plain,(
% 1.41/0.55    spl11_47 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_47])])).
% 1.41/0.55  fof(f518,plain,(
% 1.41/0.55    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl11_23 | ~spl11_47)),
% 1.41/0.55    inference(forward_demodulation,[],[f517,f257])).
% 1.41/0.55  fof(f517,plain,(
% 1.41/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl11_23 | ~spl11_47)),
% 1.41/0.55    inference(forward_demodulation,[],[f509,f257])).
% 1.41/0.55  fof(f509,plain,(
% 1.41/0.55    k1_xboole_0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl11_47),
% 1.41/0.55    inference(superposition,[],[f74,f446])).
% 1.41/0.55  fof(f446,plain,(
% 1.41/0.55    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~spl11_47),
% 1.41/0.55    inference(avatar_component_clause,[],[f445])).
% 1.41/0.55  fof(f74,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.55    inference(cnf_transformation,[],[f24])).
% 1.41/0.55  fof(f24,plain,(
% 1.41/0.55    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.55    inference(ennf_transformation,[],[f9])).
% 1.41/0.55  fof(f9,axiom,(
% 1.41/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.41/0.55  fof(f454,plain,(
% 1.41/0.55    spl11_21 | ~spl11_2 | ~spl11_19),
% 1.41/0.55    inference(avatar_split_clause,[],[f239,f234,f104,f246])).
% 1.41/0.55  fof(f246,plain,(
% 1.41/0.55    spl11_21 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).
% 1.41/0.55  fof(f104,plain,(
% 1.41/0.55    spl11_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.41/0.55  fof(f234,plain,(
% 1.41/0.55    spl11_19 <=> k1_xboole_0 = sK1),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).
% 1.41/0.55  fof(f239,plain,(
% 1.41/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl11_2 | ~spl11_19)),
% 1.41/0.55    inference(superposition,[],[f105,f235])).
% 1.41/0.55  fof(f235,plain,(
% 1.41/0.55    k1_xboole_0 = sK1 | ~spl11_19),
% 1.41/0.55    inference(avatar_component_clause,[],[f234])).
% 1.41/0.55  fof(f105,plain,(
% 1.41/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl11_2),
% 1.41/0.55    inference(avatar_component_clause,[],[f104])).
% 1.41/0.55  fof(f449,plain,(
% 1.41/0.55    k1_xboole_0 != sK1 | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | k1_xboole_0 != sK0 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.41/0.55    introduced(theory_tautology_sat_conflict,[])).
% 1.41/0.55  fof(f448,plain,(
% 1.41/0.55    spl11_47 | ~spl11_40 | ~spl11_41),
% 1.41/0.55    inference(avatar_split_clause,[],[f441,f371,f366,f445])).
% 1.41/0.55  fof(f371,plain,(
% 1.41/0.55    spl11_41 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_41])])).
% 1.41/0.55  fof(f441,plain,(
% 1.41/0.55    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~spl11_41),
% 1.41/0.55    inference(resolution,[],[f372,f97])).
% 1.41/0.55  fof(f97,plain,(
% 1.41/0.55    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 1.41/0.55    inference(equality_resolution,[],[f76])).
% 1.41/0.55  fof(f76,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.55    inference(cnf_transformation,[],[f44])).
% 1.41/0.55  fof(f372,plain,(
% 1.41/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl11_41),
% 1.41/0.55    inference(avatar_component_clause,[],[f371])).
% 1.41/0.55  fof(f414,plain,(
% 1.41/0.55    ~spl11_8 | ~spl11_11 | ~spl11_42),
% 1.41/0.55    inference(avatar_split_clause,[],[f412,f383,f171,f144])).
% 1.41/0.55  fof(f144,plain,(
% 1.41/0.55    spl11_8 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 1.41/0.55  fof(f171,plain,(
% 1.41/0.55    spl11_11 <=> ! [X0] : (sK4 != X0 | ~r2_hidden(X0,k9_relat_1(sK3,sK2)) | ~r2_hidden(sK7(sK3,sK2,X0),sK0))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 1.41/0.55  fof(f383,plain,(
% 1.41/0.55    spl11_42 <=> ! [X1,X0] : (r2_hidden(sK7(sK3,X0,X1),sK0) | ~r2_hidden(X1,k9_relat_1(sK3,X0)))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_42])])).
% 1.41/0.55  fof(f412,plain,(
% 1.41/0.55    ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl11_11 | ~spl11_42)),
% 1.41/0.55    inference(equality_resolution,[],[f398])).
% 1.41/0.55  fof(f398,plain,(
% 1.41/0.55    ( ! [X0] : (sK4 != X0 | ~r2_hidden(X0,k9_relat_1(sK3,sK2))) ) | (~spl11_11 | ~spl11_42)),
% 1.41/0.55    inference(subsumption_resolution,[],[f172,f384])).
% 1.41/0.55  fof(f384,plain,(
% 1.41/0.55    ( ! [X0,X1] : (r2_hidden(sK7(sK3,X0,X1),sK0) | ~r2_hidden(X1,k9_relat_1(sK3,X0))) ) | ~spl11_42),
% 1.41/0.55    inference(avatar_component_clause,[],[f383])).
% 1.41/0.55  fof(f172,plain,(
% 1.41/0.55    ( ! [X0] : (~r2_hidden(sK7(sK3,sK2,X0),sK0) | ~r2_hidden(X0,k9_relat_1(sK3,sK2)) | sK4 != X0) ) | ~spl11_11),
% 1.41/0.55    inference(avatar_component_clause,[],[f171])).
% 1.41/0.55  fof(f405,plain,(
% 1.41/0.55    spl11_35),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f404])).
% 1.41/0.55  fof(f404,plain,(
% 1.41/0.55    $false | spl11_35),
% 1.41/0.55    inference(subsumption_resolution,[],[f67,f402])).
% 1.41/0.55  fof(f402,plain,(
% 1.41/0.55    ( ! [X0] : (~v1_relat_1(X0)) ) | spl11_35),
% 1.41/0.55    inference(resolution,[],[f401,f57])).
% 1.41/0.55  fof(f401,plain,(
% 1.41/0.55    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~v1_relat_1(X0)) ) | spl11_35),
% 1.41/0.55    inference(resolution,[],[f354,f69])).
% 1.41/0.55  fof(f354,plain,(
% 1.41/0.55    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl11_35),
% 1.41/0.55    inference(resolution,[],[f341,f58])).
% 1.41/0.55  fof(f58,plain,(
% 1.41/0.55    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f18])).
% 1.41/0.55  fof(f18,plain,(
% 1.41/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.41/0.55    inference(ennf_transformation,[],[f4])).
% 1.41/0.55  fof(f4,axiom,(
% 1.41/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.41/0.55  fof(f341,plain,(
% 1.41/0.55    ~v1_relat_1(k1_xboole_0) | spl11_35),
% 1.41/0.55    inference(avatar_component_clause,[],[f340])).
% 1.41/0.55  fof(f67,plain,(
% 1.41/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.41/0.55    inference(cnf_transformation,[],[f5])).
% 1.41/0.55  fof(f5,axiom,(
% 1.41/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.41/0.55  fof(f385,plain,(
% 1.41/0.55    ~spl11_5 | ~spl11_4 | spl11_42 | ~spl11_39),
% 1.41/0.55    inference(avatar_split_clause,[],[f379,f360,f383,f112,f117])).
% 1.41/0.55  fof(f117,plain,(
% 1.41/0.55    spl11_5 <=> v1_relat_1(sK3)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 1.41/0.55  fof(f112,plain,(
% 1.41/0.55    spl11_4 <=> v1_funct_1(sK3)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 1.41/0.55  fof(f360,plain,(
% 1.41/0.55    spl11_39 <=> sK0 = k1_relat_1(sK3)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_39])])).
% 1.41/0.55  fof(f379,plain,(
% 1.41/0.55    ( ! [X0,X1] : (r2_hidden(sK7(sK3,X0,X1),sK0) | ~r2_hidden(X1,k9_relat_1(sK3,X0)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | ~spl11_39),
% 1.41/0.55    inference(superposition,[],[f92,f361])).
% 1.41/0.55  fof(f361,plain,(
% 1.41/0.55    sK0 = k1_relat_1(sK3) | ~spl11_39),
% 1.41/0.55    inference(avatar_component_clause,[],[f360])).
% 1.41/0.55  fof(f373,plain,(
% 1.41/0.55    spl11_41 | ~spl11_21 | ~spl11_24),
% 1.41/0.55    inference(avatar_split_clause,[],[f369,f259,f246,f371])).
% 1.41/0.55  fof(f259,plain,(
% 1.41/0.55    spl11_24 <=> k1_xboole_0 = sK0),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).
% 1.41/0.55  fof(f369,plain,(
% 1.41/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl11_21 | ~spl11_24)),
% 1.41/0.55    inference(forward_demodulation,[],[f247,f260])).
% 1.41/0.55  fof(f260,plain,(
% 1.41/0.55    k1_xboole_0 = sK0 | ~spl11_24),
% 1.41/0.55    inference(avatar_component_clause,[],[f259])).
% 1.41/0.55  fof(f247,plain,(
% 1.41/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl11_21),
% 1.41/0.55    inference(avatar_component_clause,[],[f246])).
% 1.41/0.55  fof(f368,plain,(
% 1.41/0.55    spl11_40 | ~spl11_22 | ~spl11_24),
% 1.41/0.55    inference(avatar_split_clause,[],[f364,f259,f250,f366])).
% 1.41/0.55  fof(f250,plain,(
% 1.41/0.55    spl11_22 <=> v1_funct_2(sK3,sK0,k1_xboole_0)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).
% 1.41/0.55  fof(f364,plain,(
% 1.41/0.55    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl11_22 | ~spl11_24)),
% 1.41/0.55    inference(forward_demodulation,[],[f251,f260])).
% 1.41/0.55  fof(f251,plain,(
% 1.41/0.55    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl11_22),
% 1.41/0.55    inference(avatar_component_clause,[],[f250])).
% 1.41/0.55  fof(f363,plain,(
% 1.41/0.55    ~spl11_2 | spl11_39 | ~spl11_18),
% 1.41/0.55    inference(avatar_split_clause,[],[f358,f231,f360,f104])).
% 1.41/0.55  fof(f231,plain,(
% 1.41/0.55    spl11_18 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).
% 1.41/0.55  fof(f358,plain,(
% 1.41/0.55    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl11_18),
% 1.41/0.55    inference(superposition,[],[f74,f232])).
% 1.41/0.55  fof(f232,plain,(
% 1.41/0.55    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl11_18),
% 1.41/0.55    inference(avatar_component_clause,[],[f231])).
% 1.41/0.55  fof(f349,plain,(
% 1.41/0.55    ~spl11_35 | spl11_37 | ~spl11_28),
% 1.41/0.55    inference(avatar_split_clause,[],[f337,f303,f347,f340])).
% 1.41/0.55  fof(f337,plain,(
% 1.41/0.55    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(k1_xboole_0)) | r2_hidden(k4_tarski(X2,k1_funct_1(k1_xboole_0,X2)),k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl11_28),
% 1.41/0.55    inference(resolution,[],[f304,f98])).
% 1.41/0.55  fof(f98,plain,(
% 1.41/0.55    ( ! [X2,X0] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~v1_relat_1(X2)) )),
% 1.41/0.55    inference(equality_resolution,[],[f86])).
% 1.41/0.55  fof(f86,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f51])).
% 1.41/0.55  fof(f51,plain,(
% 1.41/0.55    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.41/0.55    inference(flattening,[],[f50])).
% 1.41/0.55  fof(f50,plain,(
% 1.41/0.55    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.41/0.55    inference(nnf_transformation,[],[f29])).
% 1.41/0.55  fof(f29,plain,(
% 1.41/0.55    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.41/0.55    inference(flattening,[],[f28])).
% 1.41/0.55  fof(f28,plain,(
% 1.41/0.55    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.41/0.55    inference(ennf_transformation,[],[f8])).
% 1.41/0.55  fof(f8,axiom,(
% 1.41/0.55    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.41/0.55  fof(f304,plain,(
% 1.41/0.55    v1_funct_1(k1_xboole_0) | ~spl11_28),
% 1.41/0.55    inference(avatar_component_clause,[],[f303])).
% 1.41/0.55  fof(f309,plain,(
% 1.41/0.55    spl11_29 | ~spl11_8 | ~spl11_23),
% 1.41/0.55    inference(avatar_split_clause,[],[f271,f256,f144,f307])).
% 1.41/0.55  fof(f271,plain,(
% 1.41/0.55    r2_hidden(sK4,k9_relat_1(k1_xboole_0,sK2)) | (~spl11_8 | ~spl11_23)),
% 1.41/0.55    inference(superposition,[],[f145,f257])).
% 1.41/0.55  fof(f145,plain,(
% 1.41/0.55    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl11_8),
% 1.41/0.55    inference(avatar_component_clause,[],[f144])).
% 1.41/0.55  fof(f305,plain,(
% 1.41/0.55    spl11_28 | ~spl11_4 | ~spl11_23),
% 1.41/0.55    inference(avatar_split_clause,[],[f267,f256,f112,f303])).
% 1.41/0.55  fof(f267,plain,(
% 1.41/0.55    v1_funct_1(k1_xboole_0) | (~spl11_4 | ~spl11_23)),
% 1.41/0.55    inference(superposition,[],[f113,f257])).
% 1.41/0.55  fof(f113,plain,(
% 1.41/0.55    v1_funct_1(sK3) | ~spl11_4),
% 1.41/0.55    inference(avatar_component_clause,[],[f112])).
% 1.41/0.55  fof(f262,plain,(
% 1.41/0.55    spl11_23 | spl11_24 | ~spl11_22 | ~spl11_21),
% 1.41/0.55    inference(avatar_split_clause,[],[f253,f246,f250,f259,f256])).
% 1.41/0.55  fof(f253,plain,(
% 1.41/0.55    ~v1_funct_2(sK3,sK0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~spl11_21),
% 1.41/0.55    inference(resolution,[],[f247,f95])).
% 1.41/0.55  fof(f95,plain,(
% 1.41/0.55    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 1.41/0.55    inference(equality_resolution,[],[f79])).
% 1.41/0.55  fof(f79,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.55    inference(cnf_transformation,[],[f44])).
% 1.41/0.55  fof(f252,plain,(
% 1.41/0.55    spl11_22 | ~spl11_3 | ~spl11_19),
% 1.41/0.55    inference(avatar_split_clause,[],[f240,f234,f108,f250])).
% 1.41/0.55  fof(f108,plain,(
% 1.41/0.55    spl11_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 1.41/0.55  fof(f240,plain,(
% 1.41/0.55    v1_funct_2(sK3,sK0,k1_xboole_0) | (~spl11_3 | ~spl11_19)),
% 1.41/0.55    inference(superposition,[],[f109,f235])).
% 1.41/0.55  fof(f109,plain,(
% 1.41/0.55    v1_funct_2(sK3,sK0,sK1) | ~spl11_3),
% 1.41/0.55    inference(avatar_component_clause,[],[f108])).
% 1.41/0.55  fof(f237,plain,(
% 1.41/0.55    spl11_18 | spl11_19 | ~spl11_3 | ~spl11_2),
% 1.41/0.55    inference(avatar_split_clause,[],[f228,f104,f108,f234,f231])).
% 1.41/0.55  fof(f228,plain,(
% 1.41/0.55    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl11_2),
% 1.41/0.55    inference(resolution,[],[f75,f105])).
% 1.41/0.55  fof(f75,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.41/0.55    inference(cnf_transformation,[],[f44])).
% 1.41/0.55  fof(f173,plain,(
% 1.41/0.55    ~spl11_5 | ~spl11_4 | spl11_11 | ~spl11_10),
% 1.41/0.55    inference(avatar_split_clause,[],[f168,f161,f171,f112,f117])).
% 1.41/0.55  fof(f168,plain,(
% 1.41/0.55    ( ! [X0] : (sK4 != X0 | ~r2_hidden(sK7(sK3,sK2,X0),sK0) | ~r2_hidden(X0,k9_relat_1(sK3,sK2)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | ~spl11_10),
% 1.41/0.55    inference(duplicate_literal_removal,[],[f166])).
% 1.41/0.55  fof(f166,plain,(
% 1.41/0.55    ( ! [X0] : (sK4 != X0 | ~r2_hidden(sK7(sK3,sK2,X0),sK0) | ~r2_hidden(X0,k9_relat_1(sK3,sK2)) | ~r2_hidden(X0,k9_relat_1(sK3,sK2)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | ~spl11_10),
% 1.41/0.55    inference(resolution,[],[f165,f91])).
% 1.41/0.55  fof(f91,plain,(
% 1.41/0.55    ( ! [X6,X0,X1] : (r2_hidden(sK7(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.55    inference(equality_resolution,[],[f60])).
% 1.41/0.55  fof(f60,plain,(
% 1.41/0.55    ( ! [X6,X2,X0,X1] : (r2_hidden(sK7(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f39])).
% 1.41/0.55  fof(f163,plain,(
% 1.41/0.55    ~spl11_5 | spl11_10 | ~spl11_4),
% 1.41/0.55    inference(avatar_split_clause,[],[f159,f112,f161,f117])).
% 1.41/0.55  fof(f159,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | k1_funct_1(sK3,sK7(sK3,X1,X0)) = X0 | ~v1_relat_1(sK3)) ) | ~spl11_4),
% 1.41/0.55    inference(resolution,[],[f90,f113])).
% 1.41/0.55  fof(f90,plain,(
% 1.41/0.55    ( ! [X6,X0,X1] : (~v1_funct_1(X0) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | k1_funct_1(X0,sK7(X0,X1,X6)) = X6 | ~v1_relat_1(X0)) )),
% 1.41/0.55    inference(equality_resolution,[],[f61])).
% 1.41/0.55  fof(f61,plain,(
% 1.41/0.55    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK7(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f39])).
% 1.41/0.55  fof(f146,plain,(
% 1.41/0.55    ~spl11_2 | spl11_8 | ~spl11_1),
% 1.41/0.55    inference(avatar_split_clause,[],[f141,f100,f144,f104])).
% 1.41/0.55  fof(f100,plain,(
% 1.41/0.55    spl11_1 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.41/0.55  fof(f141,plain,(
% 1.41/0.55    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl11_1),
% 1.41/0.55    inference(superposition,[],[f101,f87])).
% 1.41/0.55  fof(f87,plain,(
% 1.41/0.55    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.55    inference(cnf_transformation,[],[f30])).
% 1.41/0.55  fof(f30,plain,(
% 1.41/0.55    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.55    inference(ennf_transformation,[],[f10])).
% 1.41/0.55  fof(f10,axiom,(
% 1.41/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.41/0.55  fof(f101,plain,(
% 1.41/0.55    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl11_1),
% 1.41/0.55    inference(avatar_component_clause,[],[f100])).
% 1.41/0.55  fof(f132,plain,(
% 1.41/0.55    spl11_7),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f130])).
% 1.41/0.55  fof(f130,plain,(
% 1.41/0.55    $false | spl11_7),
% 1.41/0.55    inference(resolution,[],[f128,f67])).
% 1.41/0.55  fof(f128,plain,(
% 1.41/0.55    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl11_7),
% 1.41/0.55    inference(avatar_component_clause,[],[f127])).
% 1.41/0.55  fof(f127,plain,(
% 1.41/0.55    spl11_7 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 1.41/0.55  fof(f129,plain,(
% 1.41/0.55    ~spl11_7 | ~spl11_2 | spl11_5),
% 1.41/0.55    inference(avatar_split_clause,[],[f124,f117,f104,f127])).
% 1.41/0.55  fof(f124,plain,(
% 1.41/0.55    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl11_2 | spl11_5)),
% 1.41/0.55    inference(resolution,[],[f123,f105])).
% 1.41/0.55  fof(f123,plain,(
% 1.41/0.55    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl11_5),
% 1.41/0.55    inference(resolution,[],[f118,f58])).
% 1.41/0.55  fof(f118,plain,(
% 1.41/0.55    ~v1_relat_1(sK3) | spl11_5),
% 1.41/0.55    inference(avatar_component_clause,[],[f117])).
% 1.41/0.55  fof(f114,plain,(
% 1.41/0.55    spl11_4),
% 1.41/0.55    inference(avatar_split_clause,[],[f52,f112])).
% 1.41/0.55  fof(f52,plain,(
% 1.41/0.55    v1_funct_1(sK3)),
% 1.41/0.55    inference(cnf_transformation,[],[f33])).
% 1.41/0.55  fof(f110,plain,(
% 1.41/0.55    spl11_3),
% 1.41/0.55    inference(avatar_split_clause,[],[f53,f108])).
% 1.41/0.55  fof(f53,plain,(
% 1.41/0.55    v1_funct_2(sK3,sK0,sK1)),
% 1.41/0.55    inference(cnf_transformation,[],[f33])).
% 1.41/0.55  fof(f106,plain,(
% 1.41/0.55    spl11_2),
% 1.41/0.55    inference(avatar_split_clause,[],[f54,f104])).
% 1.41/0.55  fof(f54,plain,(
% 1.41/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.41/0.55    inference(cnf_transformation,[],[f33])).
% 1.41/0.55  fof(f102,plain,(
% 1.41/0.55    spl11_1),
% 1.41/0.55    inference(avatar_split_clause,[],[f55,f100])).
% 1.41/0.55  fof(f55,plain,(
% 1.41/0.55    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 1.41/0.55    inference(cnf_transformation,[],[f33])).
% 1.41/0.55  % SZS output end Proof for theBenchmark
% 1.41/0.55  % (9415)------------------------------
% 1.41/0.55  % (9415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (9415)Termination reason: Refutation
% 1.41/0.55  
% 1.41/0.55  % (9415)Memory used [KB]: 11001
% 1.41/0.55  % (9415)Time elapsed: 0.129 s
% 1.41/0.55  % (9415)------------------------------
% 1.41/0.55  % (9415)------------------------------
% 1.41/0.56  % (9408)Success in time 0.201 s
%------------------------------------------------------------------------------
