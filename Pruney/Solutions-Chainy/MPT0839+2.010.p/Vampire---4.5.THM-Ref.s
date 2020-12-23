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
% DateTime   : Thu Dec  3 12:57:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 148 expanded)
%              Number of leaves         :   23 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :  280 ( 430 expanded)
%              Number of equality atoms :   56 (  92 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f155,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f64,f85,f102,f113,f117,f131,f135,f147,f154])).

fof(f154,plain,
    ( ~ spl5_2
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | ~ spl5_2
    | spl5_13 ),
    inference(subsumption_resolution,[],[f63,f152])).

fof(f152,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_13 ),
    inference(resolution,[],[f145,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f145,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl5_13
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f63,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl5_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f147,plain,
    ( ~ spl5_13
    | spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f142,f111,f100,f144])).

fof(f100,plain,
    ( spl5_8
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f111,plain,
    ( spl5_9
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f142,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_9 ),
    inference(trivial_inequality_removal,[],[f140])).

fof(f140,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_9 ),
    inference(superposition,[],[f40,f112])).

fof(f112,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f111])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f135,plain,
    ( ~ spl5_2
    | spl5_12 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl5_2
    | spl5_12 ),
    inference(subsumption_resolution,[],[f63,f132])).

fof(f132,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
    | spl5_12 ),
    inference(resolution,[],[f130,f104])).

fof(f104,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k1_relat_1(X3),k1_zfmisc_1(X4))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(resolution,[],[f96,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f96,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(k1_relat_1(X3),k1_zfmisc_1(X4))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(resolution,[],[f94,f55])).

fof(f55,plain,(
    ! [X0,X3] :
      ( ~ r1_tarski(X3,X0)
      | r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK4(X0,X1),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r1_tarski(sK4(X0,X1),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK4(X0,X1),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( r1_tarski(sK4(X0,X1),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_relat_1(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(global_subsumption,[],[f50,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k1_relat_1(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f53,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f130,plain,
    ( ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl5_12
  <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f131,plain,
    ( ~ spl5_12
    | spl5_9
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f127,f115,f83,f111,f129])).

fof(f83,plain,
    ( spl5_6
  <=> ! [X0] :
        ( ~ r2_hidden(sK3(k1_relset_1(sK1,sK0,sK2)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f115,plain,
    ( spl5_10
  <=> k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f127,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f126,f116])).

fof(f116,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f126,plain,
    ( ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))
    | k1_xboole_0 = k1_relset_1(sK1,sK0,sK2)
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f124,f116])).

fof(f124,plain,
    ( ~ m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1))
    | k1_xboole_0 = k1_relset_1(sK1,sK0,sK2)
    | ~ spl5_6 ),
    inference(resolution,[],[f84,f42])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f84,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k1_relset_1(sK1,sK0,sK2)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK1)) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f117,plain,
    ( spl5_10
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f107,f62,f115])).

fof(f107,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f52,f63])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f113,plain,
    ( spl5_9
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f109,f80,f62,f111])).

fof(f80,plain,
    ( spl5_5
  <=> k1_xboole_0 = k1_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f109,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f107,f81])).

fof(f81,plain,
    ( k1_xboole_0 = k1_relset_1(sK1,sK0,sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f102,plain,
    ( ~ spl5_2
    | ~ spl5_8
    | spl5_1 ),
    inference(avatar_split_clause,[],[f97,f58,f100,f62])).

fof(f58,plain,
    ( spl5_1
  <=> k1_xboole_0 = k2_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f97,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl5_1 ),
    inference(superposition,[],[f59,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f59,plain,
    ( k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f85,plain,
    ( spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f78,f83,f80])).

fof(f78,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(k1_relset_1(sK1,sK0,sK2)),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
      | k1_xboole_0 = k1_relset_1(sK1,sK0,sK2) ) ),
    inference(resolution,[],[f77,f42])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relset_1(sK1,sK0,sK2))
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK1)) ) ),
    inference(resolution,[],[f54,f39])).

fof(f39,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK1)
      | ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
        | ~ m1_subset_1(X3,sK1) )
    & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
            | ~ m1_subset_1(X3,X1) )
        & k1_xboole_0 != k2_relset_1(X1,X0,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
          | ~ m1_subset_1(X3,sK1) )
      & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k2_relset_1(X1,X0,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k2_relset_1(X1,X0,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ~ ( ! [X3] :
                ( m1_subset_1(X3,X1)
               => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
            & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                    & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                  & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f64,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f37,f62])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f38,f58])).

fof(f38,plain,(
    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:19:37 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.48  % (8185)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (8182)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (8183)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (8193)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  % (8191)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (8190)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.50  % (8183)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f155,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f60,f64,f85,f102,f113,f117,f131,f135,f147,f154])).
% 0.20/0.50  fof(f154,plain,(
% 0.20/0.50    ~spl5_2 | spl5_13),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f153])).
% 0.20/0.50  fof(f153,plain,(
% 0.20/0.50    $false | (~spl5_2 | spl5_13)),
% 0.20/0.50    inference(subsumption_resolution,[],[f63,f152])).
% 0.20/0.50  fof(f152,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl5_13),
% 0.20/0.50    inference(resolution,[],[f145,f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.50  fof(f145,plain,(
% 0.20/0.50    ~v1_relat_1(sK2) | spl5_13),
% 0.20/0.50    inference(avatar_component_clause,[],[f144])).
% 0.20/0.50  fof(f144,plain,(
% 0.20/0.50    spl5_13 <=> v1_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl5_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f62])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    spl5_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.50  fof(f147,plain,(
% 0.20/0.50    ~spl5_13 | spl5_8 | ~spl5_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f142,f111,f100,f144])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    spl5_8 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    spl5_9 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.50  fof(f142,plain,(
% 0.20/0.50    k1_xboole_0 = k2_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl5_9),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f140])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl5_9),
% 0.20/0.50    inference(superposition,[],[f40,f112])).
% 0.20/0.50  fof(f112,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(sK2) | ~spl5_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f111])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.20/0.50  fof(f135,plain,(
% 0.20/0.50    ~spl5_2 | spl5_12),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f134])).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    $false | (~spl5_2 | spl5_12)),
% 0.20/0.50    inference(subsumption_resolution,[],[f63,f132])).
% 0.20/0.50  fof(f132,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | spl5_12),
% 0.20/0.50    inference(resolution,[],[f130,f104])).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    ( ! [X4,X5,X3] : (m1_subset_1(k1_relat_1(X3),k1_zfmisc_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 0.20/0.50    inference(resolution,[],[f96,f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    ( ! [X4,X5,X3] : (r2_hidden(k1_relat_1(X3),k1_zfmisc_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 0.20/0.50    inference(resolution,[],[f94,f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X0,X3] : (~r1_tarski(X3,X0) | r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(equality_resolution,[],[f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.50    inference(rectify,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_tarski(k1_relat_1(X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.20/0.50    inference(global_subsumption,[],[f50,f75])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r1_tarski(k1_relat_1(X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.20/0.50    inference(resolution,[],[f53,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.50  fof(f130,plain,(
% 0.20/0.50    ~m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) | spl5_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f129])).
% 0.20/0.50  fof(f129,plain,(
% 0.20/0.50    spl5_12 <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    ~spl5_12 | spl5_9 | ~spl5_6 | ~spl5_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f127,f115,f83,f111,f129])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    spl5_6 <=> ! [X0] : (~r2_hidden(sK3(k1_relset_1(sK1,sK0,sK2)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    spl5_10 <=> k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.50  fof(f127,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(sK2) | ~m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) | (~spl5_6 | ~spl5_10)),
% 0.20/0.50    inference(forward_demodulation,[],[f126,f116])).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) | ~spl5_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f115])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    ~m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) | k1_xboole_0 = k1_relset_1(sK1,sK0,sK2) | (~spl5_6 | ~spl5_10)),
% 0.20/0.50    inference(forward_demodulation,[],[f124,f116])).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    ~m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1)) | k1_xboole_0 = k1_relset_1(sK1,sK0,sK2) | ~spl5_6),
% 0.20/0.50    inference(resolution,[],[f84,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(sK3(k1_relset_1(sK1,sK0,sK2)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK1))) ) | ~spl5_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f83])).
% 0.20/0.50  fof(f117,plain,(
% 0.20/0.50    spl5_10 | ~spl5_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f107,f62,f115])).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) | ~spl5_2),
% 0.20/0.50    inference(resolution,[],[f52,f63])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    spl5_9 | ~spl5_2 | ~spl5_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f109,f80,f62,f111])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    spl5_5 <=> k1_xboole_0 = k1_relset_1(sK1,sK0,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(sK2) | (~spl5_2 | ~spl5_5)),
% 0.20/0.50    inference(forward_demodulation,[],[f107,f81])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relset_1(sK1,sK0,sK2) | ~spl5_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f80])).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    ~spl5_2 | ~spl5_8 | spl5_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f97,f58,f100,f62])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    spl5_1 <=> k1_xboole_0 = k2_relset_1(sK1,sK0,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    k1_xboole_0 != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl5_1),
% 0.20/0.50    inference(superposition,[],[f59,f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) | spl5_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f58])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    spl5_5 | spl5_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f78,f83,f80])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(sK3(k1_relset_1(sK1,sK0,sK2)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK1)) | k1_xboole_0 = k1_relset_1(sK1,sK0,sK2)) )),
% 0.20/0.50    inference(resolution,[],[f77,f42])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X1,k1_relset_1(sK1,sK0,sK2)) | ~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK1))) )),
% 0.20/0.50    inference(resolution,[],[f54,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X3] : (~m1_subset_1(X3,sK1) | ~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.50    inference(flattening,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ? [X0,X1,X2] : ((! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f12])).
% 0.20/0.50  fof(f12,negated_conjecture,(
% 0.20/0.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.20/0.50    inference(negated_conjecture,[],[f11])).
% 0.20/0.50  fof(f11,conjecture,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.50    inference(flattening,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    spl5_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f37,f62])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ~spl5_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f38,f58])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (8183)------------------------------
% 0.20/0.50  % (8183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (8183)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (8183)Memory used [KB]: 10746
% 0.20/0.50  % (8183)Time elapsed: 0.072 s
% 0.20/0.50  % (8183)------------------------------
% 0.20/0.50  % (8183)------------------------------
% 0.20/0.51  % (8176)Success in time 0.14 s
%------------------------------------------------------------------------------
