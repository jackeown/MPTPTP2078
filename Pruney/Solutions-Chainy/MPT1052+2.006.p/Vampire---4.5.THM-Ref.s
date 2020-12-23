%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 425 expanded)
%              Number of leaves         :   31 ( 125 expanded)
%              Depth                    :   15
%              Number of atoms          :  446 (1284 expanded)
%              Number of equality atoms :   85 ( 322 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f411,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f127,f150,f163,f174,f182,f215,f237,f251,f283,f285,f304,f322,f344,f405,f410])).

fof(f410,plain,
    ( spl5_1
    | ~ spl5_12
    | ~ spl5_25 ),
    inference(avatar_contradiction_clause,[],[f406])).

fof(f406,plain,
    ( $false
    | spl5_1
    | ~ spl5_12
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f315,f343])).

fof(f343,plain,
    ( sK0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f342])).

fof(f342,plain,
    ( spl5_25
  <=> sK0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f315,plain,
    ( sK0 != k1_relat_1(k1_xboole_0)
    | spl5_1
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f86,f206])).

fof(f206,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl5_12
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f86,plain,
    ( sK0 != k1_relat_1(sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl5_1
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f405,plain,
    ( ~ spl5_5
    | spl5_24 ),
    inference(avatar_contradiction_clause,[],[f404])).

fof(f404,plain,
    ( $false
    | ~ spl5_5
    | spl5_24 ),
    inference(subsumption_resolution,[],[f110,f400])).

fof(f400,plain,
    ( ~ v1_xboole_0(sK0)
    | spl5_24 ),
    inference(resolution,[],[f396,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f396,plain,
    ( r2_hidden(sK4(sK0,k1_relat_1(k1_xboole_0)),sK0)
    | spl5_24 ),
    inference(resolution,[],[f340,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f340,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(k1_xboole_0))
    | spl5_24 ),
    inference(avatar_component_clause,[],[f339])).

fof(f339,plain,
    ( spl5_24
  <=> r1_tarski(sK0,k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f110,plain,
    ( v1_xboole_0(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl5_5
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f344,plain,
    ( ~ spl5_24
    | spl5_25
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f337,f230,f342,f339])).

fof(f230,plain,
    ( spl5_16
  <=> r1_tarski(k1_relat_1(k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f337,plain,
    ( sK0 = k1_relat_1(k1_xboole_0)
    | ~ r1_tarski(sK0,k1_relat_1(k1_xboole_0))
    | ~ spl5_16 ),
    inference(resolution,[],[f231,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f231,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK0)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f230])).

fof(f322,plain,
    ( ~ spl5_15
    | spl5_16
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f321,f205,f230,f227])).

fof(f227,plain,
    ( spl5_15
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f321,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl5_12 ),
    inference(resolution,[],[f316,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f316,plain,
    ( v4_relat_1(k1_xboole_0,sK0)
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f96,f206])).

fof(f96,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f92,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f92,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f73,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_unfolding,[],[f63,f50])).

fof(f50,plain,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_funct_2)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1) )
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

fof(f73,plain,(
    r2_hidden(sK2,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f45,f50])).

fof(f45,plain,(
    r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ r1_tarski(k2_relat_1(sK2),sK1)
      | sK0 != k1_relat_1(sK2) )
    & r2_hidden(sK2,k1_funct_2(sK0,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(k2_relat_1(X2),X1)
          | k1_relat_1(X2) != X0 )
        & r2_hidden(X2,k1_funct_2(X0,X1))
        & v1_relat_1(X2) )
   => ( ( ~ r1_tarski(k2_relat_1(sK2),sK1)
        | sK0 != k1_relat_1(sK2) )
      & r2_hidden(sK2,k1_funct_2(sK0,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( r1_tarski(k2_relat_1(X2),X1)
          & k1_relat_1(X2) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).

fof(f304,plain,
    ( spl5_1
    | ~ spl5_4
    | ~ spl5_13
    | ~ spl5_18 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | spl5_1
    | ~ spl5_4
    | ~ spl5_13
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f252,f301])).

fof(f301,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl5_4
    | ~ spl5_13
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f300,f279])).

fof(f279,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl5_18
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f300,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl5_4
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f299,f209])).

fof(f209,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl5_13
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f299,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2)
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f98,f105])).

fof(f105,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl5_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f98,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f92,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f252,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl5_1
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f86,f209])).

fof(f285,plain,
    ( ~ spl5_4
    | ~ spl5_13
    | spl5_19 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_13
    | spl5_19 ),
    inference(subsumption_resolution,[],[f256,f282])).

fof(f282,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | spl5_19 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl5_19
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f256,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f184,f209])).

fof(f184,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f91,f105])).

fof(f91,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f73,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f50])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f283,plain,
    ( spl5_18
    | ~ spl5_19
    | ~ spl5_4
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f269,f208,f104,f281,f278])).

fof(f269,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl5_4
    | ~ spl5_13 ),
    inference(resolution,[],[f257,f83])).

fof(f83,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f257,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_4
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f185,f209])).

fof(f185,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f92,f105])).

fof(f251,plain,
    ( spl5_12
    | spl5_13
    | ~ spl5_14
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f245,f104,f211,f208,f205])).

fof(f211,plain,
    ( spl5_14
  <=> v1_funct_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f245,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl5_4 ),
    inference(resolution,[],[f185,f81])).

fof(f81,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f237,plain,
    ( ~ spl5_12
    | spl5_15 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl5_12
    | spl5_15 ),
    inference(subsumption_resolution,[],[f217,f228])).

fof(f228,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f227])).

fof(f217,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f44,f206])).

fof(f44,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f215,plain,
    ( ~ spl5_4
    | spl5_14 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | ~ spl5_4
    | spl5_14 ),
    inference(subsumption_resolution,[],[f184,f212])).

fof(f212,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f211])).

fof(f182,plain,
    ( spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f169,f112,f109])).

fof(f112,plain,
    ( spl5_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f169,plain,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f93,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f55,f50])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).

fof(f93,plain,(
    ~ v1_xboole_0(k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))) ),
    inference(resolution,[],[f73,f48])).

fof(f174,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl5_2 ),
    inference(subsumption_resolution,[],[f89,f118])).

fof(f118,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(global_subsumption,[],[f44,f117])).

fof(f117,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f97,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f97,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f92,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f89,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl5_2
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f163,plain,
    ( spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f162,f104,f101])).

fof(f101,plain,
    ( spl5_3
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f162,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(global_subsumption,[],[f91,f157])).

fof(f157,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f92,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f150,plain,
    ( ~ spl5_4
    | spl5_6 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl5_4
    | spl5_6 ),
    inference(subsumption_resolution,[],[f47,f144])).

fof(f144,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_4
    | spl5_6 ),
    inference(backward_demodulation,[],[f113,f105])).

fof(f113,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f127,plain,
    ( spl5_1
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f86,f123])).

fof(f123,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f98,f102])).

fof(f102,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f90,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f46,f88,f85])).

fof(f46,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | sK0 != k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:29:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (27196)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.48  % (27196)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (27208)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f411,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f90,f127,f150,f163,f174,f182,f215,f237,f251,f283,f285,f304,f322,f344,f405,f410])).
% 0.22/0.49  fof(f410,plain,(
% 0.22/0.49    spl5_1 | ~spl5_12 | ~spl5_25),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f406])).
% 0.22/0.49  fof(f406,plain,(
% 0.22/0.49    $false | (spl5_1 | ~spl5_12 | ~spl5_25)),
% 0.22/0.49    inference(subsumption_resolution,[],[f315,f343])).
% 0.22/0.49  fof(f343,plain,(
% 0.22/0.49    sK0 = k1_relat_1(k1_xboole_0) | ~spl5_25),
% 0.22/0.49    inference(avatar_component_clause,[],[f342])).
% 0.22/0.49  fof(f342,plain,(
% 0.22/0.49    spl5_25 <=> sK0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.22/0.49  fof(f315,plain,(
% 0.22/0.49    sK0 != k1_relat_1(k1_xboole_0) | (spl5_1 | ~spl5_12)),
% 0.22/0.49    inference(backward_demodulation,[],[f86,f206])).
% 0.22/0.49  fof(f206,plain,(
% 0.22/0.49    k1_xboole_0 = sK2 | ~spl5_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f205])).
% 0.22/0.49  fof(f205,plain,(
% 0.22/0.49    spl5_12 <=> k1_xboole_0 = sK2),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    sK0 != k1_relat_1(sK2) | spl5_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f85])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    spl5_1 <=> sK0 = k1_relat_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.49  fof(f405,plain,(
% 0.22/0.49    ~spl5_5 | spl5_24),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f404])).
% 0.22/0.49  fof(f404,plain,(
% 0.22/0.49    $false | (~spl5_5 | spl5_24)),
% 0.22/0.49    inference(subsumption_resolution,[],[f110,f400])).
% 0.22/0.49  fof(f400,plain,(
% 0.22/0.49    ~v1_xboole_0(sK0) | spl5_24),
% 0.22/0.49    inference(resolution,[],[f396,f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.49    inference(rectify,[],[f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.49    inference(nnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.49  fof(f396,plain,(
% 0.22/0.49    r2_hidden(sK4(sK0,k1_relat_1(k1_xboole_0)),sK0) | spl5_24),
% 0.22/0.49    inference(resolution,[],[f340,f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.49    inference(rectify,[],[f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.49    inference(nnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.49  fof(f340,plain,(
% 0.22/0.49    ~r1_tarski(sK0,k1_relat_1(k1_xboole_0)) | spl5_24),
% 0.22/0.49    inference(avatar_component_clause,[],[f339])).
% 0.22/0.49  fof(f339,plain,(
% 0.22/0.49    spl5_24 <=> r1_tarski(sK0,k1_relat_1(k1_xboole_0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    v1_xboole_0(sK0) | ~spl5_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f109])).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    spl5_5 <=> v1_xboole_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.49  fof(f344,plain,(
% 0.22/0.49    ~spl5_24 | spl5_25 | ~spl5_16),
% 0.22/0.49    inference(avatar_split_clause,[],[f337,f230,f342,f339])).
% 0.22/0.49  fof(f230,plain,(
% 0.22/0.49    spl5_16 <=> r1_tarski(k1_relat_1(k1_xboole_0),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.22/0.49  fof(f337,plain,(
% 0.22/0.49    sK0 = k1_relat_1(k1_xboole_0) | ~r1_tarski(sK0,k1_relat_1(k1_xboole_0)) | ~spl5_16),
% 0.22/0.49    inference(resolution,[],[f231,f58])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.49    inference(flattening,[],[f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.49  fof(f231,plain,(
% 0.22/0.49    r1_tarski(k1_relat_1(k1_xboole_0),sK0) | ~spl5_16),
% 0.22/0.49    inference(avatar_component_clause,[],[f230])).
% 0.22/0.49  fof(f322,plain,(
% 0.22/0.49    ~spl5_15 | spl5_16 | ~spl5_12),
% 0.22/0.49    inference(avatar_split_clause,[],[f321,f205,f230,f227])).
% 0.22/0.49  fof(f227,plain,(
% 0.22/0.49    spl5_15 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.22/0.49  fof(f321,plain,(
% 0.22/0.49    r1_tarski(k1_relat_1(k1_xboole_0),sK0) | ~v1_relat_1(k1_xboole_0) | ~spl5_12),
% 0.22/0.49    inference(resolution,[],[f316,f53])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.22/0.49  fof(f316,plain,(
% 0.22/0.49    v4_relat_1(k1_xboole_0,sK0) | ~spl5_12),
% 0.22/0.49    inference(backward_demodulation,[],[f96,f206])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    v4_relat_1(sK2,sK0)),
% 0.22/0.49    inference(resolution,[],[f92,f65])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.49    inference(resolution,[],[f73,f75])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f63,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,axiom,(
% 0.22/0.49    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_funct_2)).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)) | ~r2_hidden(X2,k1_funct_2(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)))),
% 0.22/0.49    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    r2_hidden(sK2,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)))),
% 0.22/0.49    inference(definition_unfolding,[],[f45,f50])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    (~r1_tarski(k2_relat_1(sK2),sK1) | sK0 != k1_relat_1(sK2)) & r2_hidden(sK2,k1_funct_2(sK0,sK1)) & v1_relat_1(sK2)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_relat_1(X2)) => ((~r1_tarski(k2_relat_1(sK2),sK1) | sK0 != k1_relat_1(sK2)) & r2_hidden(sK2,k1_funct_2(sK0,sK1)) & v1_relat_1(sK2))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_relat_1(X2))),
% 0.22/0.49    inference(flattening,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1))) & v1_relat_1(X2))),
% 0.22/0.49    inference(ennf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 0.22/0.49    inference(pure_predicate_removal,[],[f14])).
% 0.22/0.49  fof(f14,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 0.22/0.49    inference(negated_conjecture,[],[f13])).
% 0.22/0.49  fof(f13,conjecture,(
% 0.22/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).
% 0.22/0.49  fof(f304,plain,(
% 0.22/0.49    spl5_1 | ~spl5_4 | ~spl5_13 | ~spl5_18),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f302])).
% 0.22/0.49  fof(f302,plain,(
% 0.22/0.49    $false | (spl5_1 | ~spl5_4 | ~spl5_13 | ~spl5_18)),
% 0.22/0.49    inference(subsumption_resolution,[],[f252,f301])).
% 0.22/0.49  fof(f301,plain,(
% 0.22/0.49    k1_xboole_0 = k1_relat_1(sK2) | (~spl5_4 | ~spl5_13 | ~spl5_18)),
% 0.22/0.49    inference(forward_demodulation,[],[f300,f279])).
% 0.22/0.49  fof(f279,plain,(
% 0.22/0.49    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~spl5_18),
% 0.22/0.49    inference(avatar_component_clause,[],[f278])).
% 0.22/0.49  fof(f278,plain,(
% 0.22/0.49    spl5_18 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.22/0.49  fof(f300,plain,(
% 0.22/0.49    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl5_4 | ~spl5_13)),
% 0.22/0.49    inference(forward_demodulation,[],[f299,f209])).
% 0.22/0.49  fof(f209,plain,(
% 0.22/0.49    k1_xboole_0 = sK0 | ~spl5_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f208])).
% 0.22/0.49  fof(f208,plain,(
% 0.22/0.49    spl5_13 <=> k1_xboole_0 = sK0),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.22/0.49  fof(f299,plain,(
% 0.22/0.49    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2) | ~spl5_4),
% 0.22/0.49    inference(forward_demodulation,[],[f98,f105])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    k1_xboole_0 = sK1 | ~spl5_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f104])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    spl5_4 <=> k1_xboole_0 = sK1),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.49    inference(resolution,[],[f92,f64])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.50  fof(f252,plain,(
% 0.22/0.50    k1_xboole_0 != k1_relat_1(sK2) | (spl5_1 | ~spl5_13)),
% 0.22/0.50    inference(backward_demodulation,[],[f86,f209])).
% 0.22/0.50  fof(f285,plain,(
% 0.22/0.50    ~spl5_4 | ~spl5_13 | spl5_19),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f284])).
% 0.22/0.50  fof(f284,plain,(
% 0.22/0.50    $false | (~spl5_4 | ~spl5_13 | spl5_19)),
% 0.22/0.50    inference(subsumption_resolution,[],[f256,f282])).
% 0.22/0.50  fof(f282,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | spl5_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f281])).
% 0.22/0.50  fof(f281,plain,(
% 0.22/0.50    spl5_19 <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.22/0.50  fof(f256,plain,(
% 0.22/0.50    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl5_4 | ~spl5_13)),
% 0.22/0.50    inference(backward_demodulation,[],[f184,f209])).
% 0.22/0.50  fof(f184,plain,(
% 0.22/0.50    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl5_4),
% 0.22/0.50    inference(backward_demodulation,[],[f91,f105])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.50    inference(resolution,[],[f73,f76])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) | v1_funct_2(X2,X0,X1)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f62,f50])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f283,plain,(
% 0.22/0.50    spl5_18 | ~spl5_19 | ~spl5_4 | ~spl5_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f269,f208,f104,f281,f278])).
% 0.22/0.50  fof(f269,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl5_4 | ~spl5_13)),
% 0.22/0.50    inference(resolution,[],[f257,f83])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.22/0.50    inference(equality_resolution,[],[f68])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(nnf_transformation,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(flattening,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.50  fof(f257,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl5_4 | ~spl5_13)),
% 0.22/0.50    inference(backward_demodulation,[],[f185,f209])).
% 0.22/0.50  fof(f185,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl5_4),
% 0.22/0.50    inference(backward_demodulation,[],[f92,f105])).
% 0.22/0.50  fof(f251,plain,(
% 0.22/0.50    spl5_12 | spl5_13 | ~spl5_14 | ~spl5_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f245,f104,f211,f208,f205])).
% 0.22/0.50  fof(f211,plain,(
% 0.22/0.50    spl5_14 <=> v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.22/0.50  fof(f245,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,sK0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl5_4),
% 0.22/0.50    inference(resolution,[],[f185,f81])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 0.22/0.50    inference(equality_resolution,[],[f71])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f43])).
% 0.22/0.50  fof(f237,plain,(
% 0.22/0.50    ~spl5_12 | spl5_15),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f236])).
% 0.22/0.50  fof(f236,plain,(
% 0.22/0.50    $false | (~spl5_12 | spl5_15)),
% 0.22/0.50    inference(subsumption_resolution,[],[f217,f228])).
% 0.22/0.50  fof(f228,plain,(
% 0.22/0.50    ~v1_relat_1(k1_xboole_0) | spl5_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f227])).
% 0.22/0.50  fof(f217,plain,(
% 0.22/0.50    v1_relat_1(k1_xboole_0) | ~spl5_12),
% 0.22/0.50    inference(backward_demodulation,[],[f44,f206])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    v1_relat_1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f215,plain,(
% 0.22/0.50    ~spl5_4 | spl5_14),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f214])).
% 0.22/0.50  fof(f214,plain,(
% 0.22/0.50    $false | (~spl5_4 | spl5_14)),
% 0.22/0.50    inference(subsumption_resolution,[],[f184,f212])).
% 0.22/0.50  fof(f212,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,sK0,k1_xboole_0) | spl5_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f211])).
% 0.22/0.50  fof(f182,plain,(
% 0.22/0.50    spl5_5 | ~spl5_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f169,f112,f109])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    spl5_6 <=> v1_xboole_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    ~v1_xboole_0(sK1) | v1_xboole_0(sK0)),
% 0.22/0.50    inference(resolution,[],[f93,f74])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f55,f50])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.22/0.50    inference(flattening,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k1_funct_2(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    ~v1_xboole_0(k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)))),
% 0.22/0.50    inference(resolution,[],[f73,f48])).
% 0.22/0.50  fof(f174,plain,(
% 0.22/0.50    spl5_2),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f170])).
% 0.22/0.50  fof(f170,plain,(
% 0.22/0.50    $false | spl5_2),
% 0.22/0.50    inference(subsumption_resolution,[],[f89,f118])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.22/0.50    inference(global_subsumption,[],[f44,f117])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    r1_tarski(k2_relat_1(sK2),sK1) | ~v1_relat_1(sK2)),
% 0.22/0.50    inference(resolution,[],[f97,f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    v5_relat_1(sK2,sK1)),
% 0.22/0.50    inference(resolution,[],[f92,f66])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    ~r1_tarski(k2_relat_1(sK2),sK1) | spl5_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f88])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    spl5_2 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.50  fof(f163,plain,(
% 0.22/0.50    spl5_3 | spl5_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f162,f104,f101])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    spl5_3 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.50    inference(global_subsumption,[],[f91,f157])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.50    inference(resolution,[],[f92,f67])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f43])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    ~spl5_4 | spl5_6),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f149])).
% 0.22/0.50  fof(f149,plain,(
% 0.22/0.50    $false | (~spl5_4 | spl5_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f47,f144])).
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    ~v1_xboole_0(k1_xboole_0) | (~spl5_4 | spl5_6)),
% 0.22/0.50    inference(backward_demodulation,[],[f113,f105])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    ~v1_xboole_0(sK1) | spl5_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f112])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    spl5_1 | ~spl5_3),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f124])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    $false | (spl5_1 | ~spl5_3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f86,f123])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    sK0 = k1_relat_1(sK2) | ~spl5_3),
% 0.22/0.50    inference(forward_demodulation,[],[f98,f102])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl5_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f101])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    ~spl5_1 | ~spl5_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f46,f88,f85])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ~r1_tarski(k2_relat_1(sK2),sK1) | sK0 != k1_relat_1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (27196)------------------------------
% 0.22/0.50  % (27196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (27196)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (27196)Memory used [KB]: 10874
% 0.22/0.50  % (27196)Time elapsed: 0.067 s
% 0.22/0.50  % (27196)------------------------------
% 0.22/0.50  % (27196)------------------------------
% 0.22/0.50  % (27191)Success in time 0.143 s
%------------------------------------------------------------------------------
