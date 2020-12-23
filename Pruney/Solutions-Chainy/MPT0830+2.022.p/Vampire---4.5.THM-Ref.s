%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:48 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 146 expanded)
%              Number of leaves         :   29 (  56 expanded)
%              Depth                    :    8
%              Number of atoms          :  296 ( 364 expanded)
%              Number of equality atoms :   17 (  20 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f210,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f67,f81,f108,f120,f123,f126,f154,f192,f198,f204,f207,f209])).

fof(f209,plain,(
    ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | ~ spl5_14 ),
    inference(resolution,[],[f140,f41])).

fof(f41,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f140,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl5_14
  <=> v1_xboole_0(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f207,plain,
    ( ~ spl5_2
    | spl5_23 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | ~ spl5_2
    | spl5_23 ),
    inference(subsumption_resolution,[],[f66,f205])).

fof(f205,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | spl5_23 ),
    inference(resolution,[],[f203,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f55,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f203,plain,
    ( ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))
    | spl5_23 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl5_23
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f66,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl5_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f204,plain,
    ( ~ spl5_23
    | spl5_14
    | spl5_22 ),
    inference(avatar_split_clause,[],[f200,f196,f139,f202])).

fof(f196,plain,
    ( spl5_22
  <=> r2_hidden(k2_relat_1(sK3),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f200,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))
    | spl5_22 ),
    inference(resolution,[],[f197,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f197,plain,
    ( ~ r2_hidden(k2_relat_1(sK3),k1_zfmisc_1(sK2))
    | spl5_22 ),
    inference(avatar_component_clause,[],[f196])).

fof(f198,plain,
    ( ~ spl5_22
    | spl5_21 ),
    inference(avatar_split_clause,[],[f194,f190,f196])).

fof(f190,plain,
    ( spl5_21
  <=> r1_tarski(k2_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f194,plain,
    ( ~ r2_hidden(k2_relat_1(sK3),k1_zfmisc_1(sK2))
    | spl5_21 ),
    inference(resolution,[],[f191,f59])).

fof(f59,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).

fof(f37,plain,(
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

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f191,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | spl5_21 ),
    inference(avatar_component_clause,[],[f190])).

fof(f192,plain,
    ( ~ spl5_10
    | ~ spl5_11
    | ~ spl5_21
    | spl5_9 ),
    inference(avatar_split_clause,[],[f188,f106,f190,f118,f115])).

fof(f115,plain,
    ( spl5_10
  <=> v1_relat_1(k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f118,plain,
    ( spl5_11
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f106,plain,
    ( spl5_9
  <=> r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f188,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k6_relat_1(sK1))
    | spl5_9 ),
    inference(resolution,[],[f127,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f43,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f127,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),X0)
        | ~ r1_tarski(X0,sK2) )
    | spl5_9 ),
    inference(resolution,[],[f107,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f107,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f154,plain,
    ( ~ spl5_11
    | spl5_8 ),
    inference(avatar_split_clause,[],[f151,f103,f118])).

fof(f103,plain,
    ( spl5_8
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f151,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_8 ),
    inference(resolution,[],[f104,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f104,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f126,plain,
    ( ~ spl5_2
    | spl5_11 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | ~ spl5_2
    | spl5_11 ),
    inference(subsumption_resolution,[],[f66,f124])).

fof(f124,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_11 ),
    inference(resolution,[],[f119,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f119,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f118])).

fof(f123,plain,(
    spl5_10 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | spl5_10 ),
    inference(resolution,[],[f116,f42])).

fof(f42,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f116,plain,
    ( ~ v1_relat_1(k6_relat_1(sK1))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f120,plain,
    ( ~ spl5_10
    | ~ spl5_11
    | spl5_7 ),
    inference(avatar_split_clause,[],[f112,f100,f118,f115])).

fof(f100,plain,
    ( spl5_7
  <=> v1_relat_1(k7_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f112,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k6_relat_1(sK1))
    | spl5_7 ),
    inference(resolution,[],[f101,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f47,f45])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f101,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f100])).

fof(f108,plain,
    ( ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | spl5_3 ),
    inference(avatar_split_clause,[],[f88,f79,f106,f103,f100])).

fof(f79,plain,
    ( spl5_3
  <=> m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f88,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)
    | ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | spl5_3 ),
    inference(resolution,[],[f52,f80])).

fof(f80,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

% (25274)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f81,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | spl5_1 ),
    inference(avatar_split_clause,[],[f76,f61,f79,f65])).

fof(f61,plain,
    ( spl5_1
  <=> m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f76,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl5_1 ),
    inference(superposition,[],[f62,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

% (25285)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f62,plain,
    ( ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f67,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f39,f65])).

fof(f39,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f33])).

fof(f33,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
   => ( ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

fof(f63,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f40,f61])).

fof(f40,plain,(
    ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.15  % Command    : run_vampire %s %d
% 0.16/0.36  % Computer   : n008.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % WCLimit    : 600
% 0.16/0.36  % DateTime   : Tue Dec  1 10:31:30 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.23/0.48  % (25276)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.50  % (25286)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.23/0.50  % (25288)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.23/0.51  % (25279)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.23/0.52  % (25279)Refutation found. Thanks to Tanya!
% 0.23/0.52  % SZS status Theorem for theBenchmark
% 0.23/0.52  % SZS output start Proof for theBenchmark
% 0.23/0.52  fof(f210,plain,(
% 0.23/0.52    $false),
% 0.23/0.52    inference(avatar_sat_refutation,[],[f63,f67,f81,f108,f120,f123,f126,f154,f192,f198,f204,f207,f209])).
% 0.23/0.52  fof(f209,plain,(
% 0.23/0.52    ~spl5_14),
% 0.23/0.52    inference(avatar_contradiction_clause,[],[f208])).
% 0.23/0.52  fof(f208,plain,(
% 0.23/0.52    $false | ~spl5_14),
% 0.23/0.52    inference(resolution,[],[f140,f41])).
% 0.23/0.52  fof(f41,plain,(
% 0.23/0.52    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f3])).
% 0.23/0.52  fof(f3,axiom,(
% 0.23/0.52    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.23/0.52  fof(f140,plain,(
% 0.23/0.52    v1_xboole_0(k1_zfmisc_1(sK2)) | ~spl5_14),
% 0.23/0.52    inference(avatar_component_clause,[],[f139])).
% 0.23/0.52  fof(f139,plain,(
% 0.23/0.52    spl5_14 <=> v1_xboole_0(k1_zfmisc_1(sK2))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.23/0.52  fof(f207,plain,(
% 0.23/0.52    ~spl5_2 | spl5_23),
% 0.23/0.52    inference(avatar_contradiction_clause,[],[f206])).
% 0.23/0.52  fof(f206,plain,(
% 0.23/0.52    $false | (~spl5_2 | spl5_23)),
% 0.23/0.52    inference(subsumption_resolution,[],[f66,f205])).
% 0.23/0.52  fof(f205,plain,(
% 0.23/0.52    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) ) | spl5_23),
% 0.23/0.52    inference(resolution,[],[f203,f73])).
% 0.23/0.52  fof(f73,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.52    inference(duplicate_literal_removal,[],[f72])).
% 0.23/0.52  fof(f72,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.52    inference(superposition,[],[f55,f54])).
% 0.23/0.52  fof(f54,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f28])).
% 0.23/0.52  fof(f28,plain,(
% 0.23/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.52    inference(ennf_transformation,[],[f12])).
% 0.23/0.52  fof(f12,axiom,(
% 0.23/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.23/0.52  fof(f55,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f29])).
% 0.23/0.52  fof(f29,plain,(
% 0.23/0.52    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.52    inference(ennf_transformation,[],[f11])).
% 0.23/0.52  fof(f11,axiom,(
% 0.23/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.23/0.52  fof(f203,plain,(
% 0.23/0.52    ~m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) | spl5_23),
% 0.23/0.52    inference(avatar_component_clause,[],[f202])).
% 0.23/0.52  fof(f202,plain,(
% 0.23/0.52    spl5_23 <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.23/0.52  fof(f66,plain,(
% 0.23/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl5_2),
% 0.23/0.52    inference(avatar_component_clause,[],[f65])).
% 0.23/0.52  fof(f65,plain,(
% 0.23/0.52    spl5_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.23/0.52  fof(f204,plain,(
% 0.23/0.52    ~spl5_23 | spl5_14 | spl5_22),
% 0.23/0.52    inference(avatar_split_clause,[],[f200,f196,f139,f202])).
% 0.23/0.52  fof(f196,plain,(
% 0.23/0.52    spl5_22 <=> r2_hidden(k2_relat_1(sK3),k1_zfmisc_1(sK2))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.23/0.52  fof(f200,plain,(
% 0.23/0.52    v1_xboole_0(k1_zfmisc_1(sK2)) | ~m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) | spl5_22),
% 0.23/0.52    inference(resolution,[],[f197,f46])).
% 0.23/0.52  fof(f46,plain,(
% 0.23/0.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f22])).
% 0.23/0.52  fof(f22,plain,(
% 0.23/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.23/0.52    inference(flattening,[],[f21])).
% 0.23/0.52  fof(f21,plain,(
% 0.23/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.23/0.52    inference(ennf_transformation,[],[f4])).
% 0.23/0.52  fof(f4,axiom,(
% 0.23/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.23/0.52  fof(f197,plain,(
% 0.23/0.52    ~r2_hidden(k2_relat_1(sK3),k1_zfmisc_1(sK2)) | spl5_22),
% 0.23/0.52    inference(avatar_component_clause,[],[f196])).
% 0.23/0.52  fof(f198,plain,(
% 0.23/0.52    ~spl5_22 | spl5_21),
% 0.23/0.52    inference(avatar_split_clause,[],[f194,f190,f196])).
% 0.23/0.52  fof(f190,plain,(
% 0.23/0.52    spl5_21 <=> r1_tarski(k2_relat_1(sK3),sK2)),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.23/0.52  fof(f194,plain,(
% 0.23/0.52    ~r2_hidden(k2_relat_1(sK3),k1_zfmisc_1(sK2)) | spl5_21),
% 0.23/0.52    inference(resolution,[],[f191,f59])).
% 0.23/0.52  fof(f59,plain,(
% 0.23/0.52    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.23/0.52    inference(equality_resolution,[],[f48])).
% 0.23/0.52  fof(f48,plain,(
% 0.23/0.52    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.23/0.52    inference(cnf_transformation,[],[f38])).
% 0.23/0.52  fof(f38,plain,(
% 0.23/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.23/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 0.23/0.52  fof(f37,plain,(
% 0.23/0.52    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 0.23/0.52    introduced(choice_axiom,[])).
% 0.23/0.52  fof(f36,plain,(
% 0.23/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.23/0.52    inference(rectify,[],[f35])).
% 0.23/0.52  fof(f35,plain,(
% 0.23/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.23/0.52    inference(nnf_transformation,[],[f2])).
% 0.23/0.52  fof(f2,axiom,(
% 0.23/0.52    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.23/0.52  fof(f191,plain,(
% 0.23/0.52    ~r1_tarski(k2_relat_1(sK3),sK2) | spl5_21),
% 0.23/0.52    inference(avatar_component_clause,[],[f190])).
% 0.23/0.52  fof(f192,plain,(
% 0.23/0.52    ~spl5_10 | ~spl5_11 | ~spl5_21 | spl5_9),
% 0.23/0.52    inference(avatar_split_clause,[],[f188,f106,f190,f118,f115])).
% 0.23/0.52  fof(f115,plain,(
% 0.23/0.52    spl5_10 <=> v1_relat_1(k6_relat_1(sK1))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.23/0.52  fof(f118,plain,(
% 0.23/0.52    spl5_11 <=> v1_relat_1(sK3)),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.23/0.52  fof(f106,plain,(
% 0.23/0.52    spl5_9 <=> r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2)),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.23/0.52  fof(f188,plain,(
% 0.23/0.52    ~r1_tarski(k2_relat_1(sK3),sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k6_relat_1(sK1)) | spl5_9),
% 0.23/0.52    inference(resolution,[],[f127,f71])).
% 0.23/0.52  fof(f71,plain,(
% 0.23/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.23/0.52    inference(duplicate_literal_removal,[],[f70])).
% 0.23/0.52  fof(f70,plain,(
% 0.23/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.23/0.52    inference(superposition,[],[f43,f45])).
% 0.23/0.52  fof(f45,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f20])).
% 0.23/0.52  fof(f20,plain,(
% 0.23/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.23/0.52    inference(ennf_transformation,[],[f9])).
% 0.23/0.52  fof(f9,axiom,(
% 0.23/0.52    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.23/0.52  fof(f43,plain,(
% 0.23/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f18])).
% 0.23/0.52  fof(f18,plain,(
% 0.23/0.52    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.23/0.52    inference(ennf_transformation,[],[f7])).
% 0.23/0.52  fof(f7,axiom,(
% 0.23/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 0.23/0.52  fof(f127,plain,(
% 0.23/0.52    ( ! [X0] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),X0) | ~r1_tarski(X0,sK2)) ) | spl5_9),
% 0.23/0.52    inference(resolution,[],[f107,f56])).
% 0.23/0.52  fof(f56,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f31])).
% 0.23/0.52  fof(f31,plain,(
% 0.23/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.23/0.52    inference(flattening,[],[f30])).
% 0.23/0.52  fof(f30,plain,(
% 0.23/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.23/0.52    inference(ennf_transformation,[],[f1])).
% 0.23/0.52  fof(f1,axiom,(
% 0.23/0.52    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.23/0.52  fof(f107,plain,(
% 0.23/0.52    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) | spl5_9),
% 0.23/0.52    inference(avatar_component_clause,[],[f106])).
% 0.23/0.52  fof(f154,plain,(
% 0.23/0.52    ~spl5_11 | spl5_8),
% 0.23/0.52    inference(avatar_split_clause,[],[f151,f103,f118])).
% 0.23/0.52  fof(f103,plain,(
% 0.23/0.52    spl5_8 <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.23/0.52  fof(f151,plain,(
% 0.23/0.52    ~v1_relat_1(sK3) | spl5_8),
% 0.23/0.52    inference(resolution,[],[f104,f44])).
% 0.23/0.52  fof(f44,plain,(
% 0.23/0.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f19])).
% 0.23/0.52  fof(f19,plain,(
% 0.23/0.52    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.23/0.52    inference(ennf_transformation,[],[f8])).
% 0.23/0.52  fof(f8,axiom,(
% 0.23/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.23/0.52  fof(f104,plain,(
% 0.23/0.52    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) | spl5_8),
% 0.23/0.52    inference(avatar_component_clause,[],[f103])).
% 0.23/0.52  fof(f126,plain,(
% 0.23/0.52    ~spl5_2 | spl5_11),
% 0.23/0.52    inference(avatar_contradiction_clause,[],[f125])).
% 0.23/0.52  fof(f125,plain,(
% 0.23/0.52    $false | (~spl5_2 | spl5_11)),
% 0.23/0.52    inference(subsumption_resolution,[],[f66,f124])).
% 0.23/0.52  fof(f124,plain,(
% 0.23/0.52    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl5_11),
% 0.23/0.52    inference(resolution,[],[f119,f53])).
% 0.23/0.52  fof(f53,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f27])).
% 0.23/0.52  fof(f27,plain,(
% 0.23/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.52    inference(ennf_transformation,[],[f10])).
% 0.23/0.52  fof(f10,axiom,(
% 0.23/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.23/0.52  fof(f119,plain,(
% 0.23/0.52    ~v1_relat_1(sK3) | spl5_11),
% 0.23/0.52    inference(avatar_component_clause,[],[f118])).
% 0.23/0.52  fof(f123,plain,(
% 0.23/0.52    spl5_10),
% 0.23/0.52    inference(avatar_contradiction_clause,[],[f121])).
% 0.23/0.52  fof(f121,plain,(
% 0.23/0.52    $false | spl5_10),
% 0.23/0.52    inference(resolution,[],[f116,f42])).
% 0.23/0.52  fof(f42,plain,(
% 0.23/0.52    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f6])).
% 0.23/0.52  fof(f6,axiom,(
% 0.23/0.52    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.23/0.52  fof(f116,plain,(
% 0.23/0.52    ~v1_relat_1(k6_relat_1(sK1)) | spl5_10),
% 0.23/0.52    inference(avatar_component_clause,[],[f115])).
% 0.23/0.52  fof(f120,plain,(
% 0.23/0.52    ~spl5_10 | ~spl5_11 | spl5_7),
% 0.23/0.52    inference(avatar_split_clause,[],[f112,f100,f118,f115])).
% 0.23/0.52  fof(f100,plain,(
% 0.23/0.52    spl5_7 <=> v1_relat_1(k7_relat_1(sK3,sK1))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.23/0.52  fof(f112,plain,(
% 0.23/0.52    ~v1_relat_1(sK3) | ~v1_relat_1(k6_relat_1(sK1)) | spl5_7),
% 0.23/0.52    inference(resolution,[],[f101,f69])).
% 0.23/0.52  fof(f69,plain,(
% 0.23/0.52    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.23/0.52    inference(duplicate_literal_removal,[],[f68])).
% 0.23/0.52  fof(f68,plain,(
% 0.23/0.52    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.23/0.52    inference(superposition,[],[f47,f45])).
% 0.23/0.52  fof(f47,plain,(
% 0.23/0.52    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f24])).
% 0.23/0.52  fof(f24,plain,(
% 0.23/0.52    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.23/0.52    inference(flattening,[],[f23])).
% 0.23/0.52  fof(f23,plain,(
% 0.23/0.52    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.23/0.52    inference(ennf_transformation,[],[f5])).
% 0.23/0.52  fof(f5,axiom,(
% 0.23/0.52    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.23/0.52  fof(f101,plain,(
% 0.23/0.52    ~v1_relat_1(k7_relat_1(sK3,sK1)) | spl5_7),
% 0.23/0.52    inference(avatar_component_clause,[],[f100])).
% 0.23/0.52  fof(f108,plain,(
% 0.23/0.52    ~spl5_7 | ~spl5_8 | ~spl5_9 | spl5_3),
% 0.23/0.52    inference(avatar_split_clause,[],[f88,f79,f106,f103,f100])).
% 0.23/0.52  fof(f79,plain,(
% 0.23/0.52    spl5_3 <=> m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.23/0.52  fof(f88,plain,(
% 0.23/0.52    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) | ~v1_relat_1(k7_relat_1(sK3,sK1)) | spl5_3),
% 0.23/0.52    inference(resolution,[],[f52,f80])).
% 0.23/0.52  fof(f80,plain,(
% 0.23/0.52    ~m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_3),
% 0.23/0.52    inference(avatar_component_clause,[],[f79])).
% 0.23/0.52  fof(f52,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f26])).
% 0.23/0.52  fof(f26,plain,(
% 0.23/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.23/0.52    inference(flattening,[],[f25])).
% 0.23/0.52  fof(f25,plain,(
% 0.23/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.23/0.52    inference(ennf_transformation,[],[f14])).
% 0.23/0.52  fof(f14,axiom,(
% 0.23/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.23/0.52  % (25274)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.23/0.52  fof(f81,plain,(
% 0.23/0.52    ~spl5_2 | ~spl5_3 | spl5_1),
% 0.23/0.52    inference(avatar_split_clause,[],[f76,f61,f79,f65])).
% 0.23/0.52  fof(f61,plain,(
% 0.23/0.52    spl5_1 <=> m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.23/0.52  fof(f76,plain,(
% 0.23/0.52    ~m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl5_1),
% 0.23/0.52    inference(superposition,[],[f62,f57])).
% 0.23/0.52  fof(f57,plain,(
% 0.23/0.52    ( ! [X2,X0,X3,X1] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f32])).
% 0.23/0.52  % (25285)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.52  fof(f32,plain,(
% 0.23/0.52    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.52    inference(ennf_transformation,[],[f13])).
% 0.23/0.52  fof(f13,axiom,(
% 0.23/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.23/0.52  fof(f62,plain,(
% 0.23/0.52    ~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_1),
% 0.23/0.52    inference(avatar_component_clause,[],[f61])).
% 0.23/0.52  fof(f67,plain,(
% 0.23/0.52    spl5_2),
% 0.23/0.52    inference(avatar_split_clause,[],[f39,f65])).
% 0.23/0.52  fof(f39,plain,(
% 0.23/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.23/0.52    inference(cnf_transformation,[],[f34])).
% 0.23/0.52  fof(f34,plain,(
% 0.23/0.52    ~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.23/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f33])).
% 0.23/0.52  fof(f33,plain,(
% 0.23/0.52    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) => (~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))))),
% 0.23/0.52    introduced(choice_axiom,[])).
% 0.23/0.52  fof(f17,plain,(
% 0.23/0.52    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.23/0.52    inference(ennf_transformation,[],[f16])).
% 0.23/0.52  fof(f16,negated_conjecture,(
% 0.23/0.52    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.23/0.52    inference(negated_conjecture,[],[f15])).
% 0.23/0.52  fof(f15,conjecture,(
% 0.23/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).
% 0.23/0.52  fof(f63,plain,(
% 0.23/0.52    ~spl5_1),
% 0.23/0.52    inference(avatar_split_clause,[],[f40,f61])).
% 0.23/0.52  fof(f40,plain,(
% 0.23/0.52    ~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.23/0.52    inference(cnf_transformation,[],[f34])).
% 0.23/0.52  % SZS output end Proof for theBenchmark
% 0.23/0.52  % (25279)------------------------------
% 0.23/0.52  % (25279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (25279)Termination reason: Refutation
% 0.23/0.52  
% 0.23/0.52  % (25279)Memory used [KB]: 10746
% 0.23/0.52  % (25279)Time elapsed: 0.013 s
% 0.23/0.52  % (25279)------------------------------
% 0.23/0.52  % (25279)------------------------------
% 0.23/0.52  % (25270)Success in time 0.145 s
%------------------------------------------------------------------------------
