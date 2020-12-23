%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 207 expanded)
%              Number of leaves         :   35 (  76 expanded)
%              Depth                    :   14
%              Number of atoms          :  430 ( 659 expanded)
%              Number of equality atoms :   84 ( 125 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f573,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f105,f110,f115,f120,f141,f154,f240,f304,f516,f520,f532,f551,f570])).

fof(f570,plain,
    ( ~ spl8_8
    | spl8_16
    | spl8_18
    | ~ spl8_26 ),
    inference(avatar_contradiction_clause,[],[f569])).

fof(f569,plain,
    ( $false
    | ~ spl8_8
    | spl8_16
    | spl8_18
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f568,f205])).

fof(f205,plain,
    ( k1_xboole_0 != sK2
    | spl8_16 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl8_16
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f568,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_8
    | spl8_18
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f567,f140])).

fof(f140,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl8_8
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f567,plain,
    ( ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | spl8_18
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f558,f220])).

fof(f220,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | spl8_18 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl8_18
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f558,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl8_26 ),
    inference(superposition,[],[f198,f301])).

fof(f301,plain,
    ( sK0 = sK5(sK2)
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f299])).

fof(f299,plain,
    ( spl8_26
  <=> sK0 = sK5(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f198,plain,(
    ! [X5] :
      ( r2_hidden(sK5(X5),k1_relat_1(X5))
      | ~ v1_relat_1(X5)
      | k1_xboole_0 = X5 ) ),
    inference(duplicate_literal_removal,[],[f196])).

fof(f196,plain,(
    ! [X5] :
      ( k1_xboole_0 = X5
      | ~ v1_relat_1(X5)
      | r2_hidden(sK5(X5),k1_relat_1(X5))
      | ~ v1_relat_1(X5) ) ),
    inference(resolution,[],[f72,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(f72,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f35,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
     => r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

fof(f551,plain,
    ( ~ spl8_20
    | spl8_2
    | spl8_29 ),
    inference(avatar_split_clause,[],[f548,f334,f102,f237])).

fof(f237,plain,
    ( spl8_20
  <=> v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f102,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f334,plain,
    ( spl8_29
  <=> k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f548,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1)
    | spl8_2
    | spl8_29 ),
    inference(subsumption_resolution,[],[f545,f104])).

fof(f104,plain,
    ( k1_xboole_0 != sK1
    | spl8_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f545,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1)
    | spl8_29 ),
    inference(trivial_inequality_removal,[],[f542])).

fof(f542,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1)
    | spl8_29 ),
    inference(superposition,[],[f335,f282])).

fof(f282,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X1,k1_xboole_0) = X0
      | k1_xboole_0 = X1
      | ~ v1_funct_2(k1_xboole_0,X0,X1) ) ),
    inference(resolution,[],[f73,f81])).

fof(f81,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f335,plain,
    ( k1_tarski(sK0) != k1_relset_1(k1_tarski(sK0),sK1,k1_xboole_0)
    | spl8_29 ),
    inference(avatar_component_clause,[],[f334])).

fof(f532,plain,
    ( spl8_12
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f525,f107,f167])).

fof(f167,plain,
    ( spl8_12
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(X0,k2_zfmisc_1(k1_tarski(sK0),sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f107,plain,
    ( spl8_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f525,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(X0,k2_zfmisc_1(k1_tarski(sK0),sK1)) )
    | ~ spl8_3 ),
    inference(resolution,[],[f109,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f109,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f520,plain,
    ( ~ spl8_10
    | ~ spl8_18
    | spl8_1
    | ~ spl8_5
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f519,f138,f117,f97,f218,f151])).

fof(f151,plain,
    ( spl8_10
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f97,plain,
    ( spl8_1
  <=> r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f117,plain,
    ( spl8_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f519,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v5_relat_1(sK2,sK1)
    | spl8_1
    | ~ spl8_5
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f518,f140])).

fof(f518,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | spl8_1
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f517,f119])).

fof(f119,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f117])).

fof(f517,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | spl8_1 ),
    inference(resolution,[],[f99,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(f99,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f516,plain,(
    ~ spl8_29 ),
    inference(avatar_contradiction_clause,[],[f515])).

fof(f515,plain,
    ( $false
    | ~ spl8_29 ),
    inference(subsumption_resolution,[],[f510,f121])).

fof(f121,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(superposition,[],[f88,f80])).

fof(f80,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f88,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).

fof(f510,plain,
    ( v1_xboole_0(k1_tarski(sK0))
    | ~ spl8_29 ),
    inference(resolution,[],[f495,f124])).

fof(f124,plain,(
    ! [X1] :
      ( r2_hidden(sK7(X1),X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f71,f84])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f7,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f495,plain,
    ( ! [X10] : ~ r2_hidden(X10,k1_tarski(sK0))
    | ~ spl8_29 ),
    inference(subsumption_resolution,[],[f491,f82])).

% (14099)Refutation not found, incomplete strategy% (14099)------------------------------
% (14099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14099)Termination reason: Refutation not found, incomplete strategy

% (14099)Memory used [KB]: 11001
% (14099)Time elapsed: 0.146 s
% (14099)------------------------------
% (14099)------------------------------
fof(f82,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f491,plain,
    ( ! [X10] :
        ( ~ r2_hidden(X10,k1_tarski(sK0))
        | ~ r1_tarski(k1_xboole_0,k4_tarski(X10,sK3(k1_xboole_0,X10))) )
    | ~ spl8_29 ),
    inference(resolution,[],[f380,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f380,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK3(k1_xboole_0,X0)),k1_xboole_0)
        | ~ r2_hidden(X0,k1_tarski(sK0)) )
    | ~ spl8_29 ),
    inference(subsumption_resolution,[],[f379,f81])).

fof(f379,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK0))
        | r2_hidden(k4_tarski(X0,sK3(k1_xboole_0,X0)),k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) )
    | ~ spl8_29 ),
    inference(trivial_inequality_removal,[],[f376])).

fof(f376,plain,
    ( ! [X0] :
        ( k1_tarski(sK0) != k1_tarski(sK0)
        | ~ r2_hidden(X0,k1_tarski(sK0))
        | r2_hidden(k4_tarski(X0,sK3(k1_xboole_0,X0)),k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) )
    | ~ spl8_29 ),
    inference(superposition,[],[f67,f336])).

fof(f336,plain,
    ( k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,k1_xboole_0)
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f334])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_relset_1(X1,X0,X2) != X1
      | ~ r2_hidden(X3,X1)
      | r2_hidden(k4_tarski(X3,sK3(X2,X3)),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK3(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK4(X1,X2),X6),X2)
            & r2_hidden(sK4(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f47,f49,f48])).

fof(f48,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK3(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK4(X1,X2),X6),X2)
        & r2_hidden(sK4(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

fof(f304,plain,
    ( spl8_16
    | spl8_26
    | ~ spl8_8
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f303,f167,f138,f299,f204])).

fof(f303,plain,
    ( sK0 = sK5(sK2)
    | k1_xboole_0 = sK2
    | ~ spl8_8
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f295,f140])).

fof(f295,plain,
    ( sK0 = sK5(sK2)
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2)
    | ~ spl8_12 ),
    inference(resolution,[],[f178,f72])).

fof(f178,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(k4_tarski(X3,X4),sK2)
        | sK0 = X3 )
    | ~ spl8_12 ),
    inference(resolution,[],[f168,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(f168,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(sK0),sK1))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f167])).

fof(f240,plain,
    ( spl8_20
    | ~ spl8_4
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f224,f204,f112,f237])).

fof(f112,plain,
    ( spl8_4
  <=> v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f224,plain,
    ( v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1)
    | ~ spl8_4
    | ~ spl8_16 ),
    inference(backward_demodulation,[],[f114,f206])).

fof(f206,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f204])).

fof(f114,plain,
    ( v1_funct_2(sK2,k1_tarski(sK0),sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f154,plain,
    ( spl8_10
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f147,f107,f151])).

fof(f147,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl8_3 ),
    inference(resolution,[],[f87,f109])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f141,plain,
    ( spl8_8
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f134,f107,f138])).

fof(f134,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_3 ),
    inference(resolution,[],[f83,f109])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f120,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f56,f117])).

fof(f56,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f42])).

fof(f42,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(f115,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f57,f112])).

fof(f57,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f110,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f58,f107])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f105,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f59,f102])).

fof(f59,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f100,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f60,f97])).

fof(f60,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:32:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (14081)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.50  % (14075)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (14088)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.51  % (14089)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.51  % (14080)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (14096)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.52  % (14071)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (14076)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (14097)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (14072)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (14093)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (14083)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (14085)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (14095)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.53  % (14074)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (14081)Refutation not found, incomplete strategy% (14081)------------------------------
% 0.20/0.53  % (14081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (14088)Refutation not found, incomplete strategy% (14088)------------------------------
% 0.20/0.53  % (14088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (14073)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (14088)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (14088)Memory used [KB]: 1791
% 0.20/0.53  % (14088)Time elapsed: 0.124 s
% 0.20/0.53  % (14088)------------------------------
% 0.20/0.53  % (14088)------------------------------
% 0.20/0.53  % (14092)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (14077)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (14094)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.54  % (14099)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (14085)Refutation not found, incomplete strategy% (14085)------------------------------
% 0.20/0.54  % (14085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (14085)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (14085)Memory used [KB]: 1791
% 0.20/0.54  % (14085)Time elapsed: 0.092 s
% 0.20/0.54  % (14085)------------------------------
% 0.20/0.54  % (14085)------------------------------
% 0.20/0.54  % (14081)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (14081)Memory used [KB]: 11001
% 0.20/0.54  % (14081)Time elapsed: 0.110 s
% 0.20/0.54  % (14081)------------------------------
% 0.20/0.54  % (14081)------------------------------
% 0.20/0.54  % (14098)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (14100)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (14078)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (14079)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (14100)Refutation not found, incomplete strategy% (14100)------------------------------
% 0.20/0.54  % (14100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (14100)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (14100)Memory used [KB]: 1791
% 0.20/0.54  % (14100)Time elapsed: 0.137 s
% 0.20/0.54  % (14100)------------------------------
% 0.20/0.54  % (14100)------------------------------
% 0.20/0.54  % (14091)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.55  % (14090)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (14087)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.55  % (14086)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.55  % (14087)Refutation not found, incomplete strategy% (14087)------------------------------
% 0.20/0.55  % (14087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (14087)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (14087)Memory used [KB]: 10746
% 0.20/0.55  % (14087)Time elapsed: 0.147 s
% 0.20/0.55  % (14087)------------------------------
% 0.20/0.55  % (14087)------------------------------
% 0.20/0.55  % (14084)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.55  % (14082)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.56  % (14092)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f573,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(avatar_sat_refutation,[],[f100,f105,f110,f115,f120,f141,f154,f240,f304,f516,f520,f532,f551,f570])).
% 0.20/0.56  fof(f570,plain,(
% 0.20/0.56    ~spl8_8 | spl8_16 | spl8_18 | ~spl8_26),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f569])).
% 0.20/0.56  fof(f569,plain,(
% 0.20/0.56    $false | (~spl8_8 | spl8_16 | spl8_18 | ~spl8_26)),
% 0.20/0.56    inference(subsumption_resolution,[],[f568,f205])).
% 0.20/0.56  fof(f205,plain,(
% 0.20/0.56    k1_xboole_0 != sK2 | spl8_16),
% 0.20/0.56    inference(avatar_component_clause,[],[f204])).
% 0.20/0.56  fof(f204,plain,(
% 0.20/0.56    spl8_16 <=> k1_xboole_0 = sK2),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.20/0.56  fof(f568,plain,(
% 0.20/0.56    k1_xboole_0 = sK2 | (~spl8_8 | spl8_18 | ~spl8_26)),
% 0.20/0.56    inference(subsumption_resolution,[],[f567,f140])).
% 0.20/0.56  fof(f140,plain,(
% 0.20/0.56    v1_relat_1(sK2) | ~spl8_8),
% 0.20/0.56    inference(avatar_component_clause,[],[f138])).
% 0.20/0.56  fof(f138,plain,(
% 0.20/0.56    spl8_8 <=> v1_relat_1(sK2)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.56  fof(f567,plain,(
% 0.20/0.56    ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | (spl8_18 | ~spl8_26)),
% 0.20/0.56    inference(subsumption_resolution,[],[f558,f220])).
% 0.20/0.56  fof(f220,plain,(
% 0.20/0.56    ~r2_hidden(sK0,k1_relat_1(sK2)) | spl8_18),
% 0.20/0.56    inference(avatar_component_clause,[],[f218])).
% 0.20/0.56  fof(f218,plain,(
% 0.20/0.56    spl8_18 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.20/0.56  fof(f558,plain,(
% 0.20/0.56    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | ~spl8_26),
% 0.20/0.56    inference(superposition,[],[f198,f301])).
% 0.20/0.56  fof(f301,plain,(
% 0.20/0.56    sK0 = sK5(sK2) | ~spl8_26),
% 0.20/0.56    inference(avatar_component_clause,[],[f299])).
% 0.20/0.56  fof(f299,plain,(
% 0.20/0.56    spl8_26 <=> sK0 = sK5(sK2)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.20/0.56  fof(f198,plain,(
% 0.20/0.56    ( ! [X5] : (r2_hidden(sK5(X5),k1_relat_1(X5)) | ~v1_relat_1(X5) | k1_xboole_0 = X5) )),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f196])).
% 0.20/0.56  fof(f196,plain,(
% 0.20/0.56    ( ! [X5] : (k1_xboole_0 = X5 | ~v1_relat_1(X5) | r2_hidden(sK5(X5),k1_relat_1(X5)) | ~v1_relat_1(X5)) )),
% 0.20/0.56    inference(resolution,[],[f72,f85])).
% 0.20/0.56  fof(f85,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f40])).
% 0.20/0.56  fof(f40,plain,(
% 0.20/0.56    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.20/0.56    inference(flattening,[],[f39])).
% 0.20/0.56  fof(f39,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.20/0.56    inference(ennf_transformation,[],[f12])).
% 0.20/0.56  fof(f12,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).
% 0.20/0.56  fof(f72,plain,(
% 0.20/0.56    ( ! [X0] : (r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f52])).
% 0.20/0.56  fof(f52,plain,(
% 0.20/0.56    ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f35,f51])).
% 0.20/0.56  fof(f51,plain,(
% 0.20/0.56    ! [X0] : (? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) => r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f35,plain,(
% 0.20/0.56    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(flattening,[],[f34])).
% 0.20/0.56  fof(f34,plain,(
% 0.20/0.56    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f13])).
% 0.20/0.56  fof(f13,axiom,(
% 0.20/0.56    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).
% 0.20/0.56  fof(f551,plain,(
% 0.20/0.56    ~spl8_20 | spl8_2 | spl8_29),
% 0.20/0.56    inference(avatar_split_clause,[],[f548,f334,f102,f237])).
% 0.20/0.56  fof(f237,plain,(
% 0.20/0.56    spl8_20 <=> v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.20/0.56  fof(f102,plain,(
% 0.20/0.56    spl8_2 <=> k1_xboole_0 = sK1),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.56  fof(f334,plain,(
% 0.20/0.56    spl8_29 <=> k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,k1_xboole_0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 0.20/0.56  fof(f548,plain,(
% 0.20/0.56    ~v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1) | (spl8_2 | spl8_29)),
% 0.20/0.56    inference(subsumption_resolution,[],[f545,f104])).
% 0.20/0.56  fof(f104,plain,(
% 0.20/0.56    k1_xboole_0 != sK1 | spl8_2),
% 0.20/0.56    inference(avatar_component_clause,[],[f102])).
% 0.20/0.56  fof(f545,plain,(
% 0.20/0.56    k1_xboole_0 = sK1 | ~v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1) | spl8_29),
% 0.20/0.56    inference(trivial_inequality_removal,[],[f542])).
% 0.20/0.56  fof(f542,plain,(
% 0.20/0.56    k1_tarski(sK0) != k1_tarski(sK0) | k1_xboole_0 = sK1 | ~v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1) | spl8_29),
% 0.20/0.56    inference(superposition,[],[f335,f282])).
% 0.20/0.56  fof(f282,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k1_relset_1(X0,X1,k1_xboole_0) = X0 | k1_xboole_0 = X1 | ~v1_funct_2(k1_xboole_0,X0,X1)) )),
% 0.20/0.56    inference(resolution,[],[f73,f81])).
% 0.20/0.56  fof(f81,plain,(
% 0.20/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f9])).
% 0.20/0.56  fof(f9,axiom,(
% 0.20/0.56    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.56  fof(f73,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f53])).
% 0.20/0.56  fof(f53,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.56    inference(nnf_transformation,[],[f37])).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.56    inference(flattening,[],[f36])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.56    inference(ennf_transformation,[],[f19])).
% 0.20/0.56  fof(f19,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.56  fof(f335,plain,(
% 0.20/0.56    k1_tarski(sK0) != k1_relset_1(k1_tarski(sK0),sK1,k1_xboole_0) | spl8_29),
% 0.20/0.56    inference(avatar_component_clause,[],[f334])).
% 0.20/0.56  fof(f532,plain,(
% 0.20/0.56    spl8_12 | ~spl8_3),
% 0.20/0.56    inference(avatar_split_clause,[],[f525,f107,f167])).
% 0.20/0.56  fof(f167,plain,(
% 0.20/0.56    spl8_12 <=> ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.20/0.56  fof(f107,plain,(
% 0.20/0.56    spl8_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.56  fof(f525,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,k2_zfmisc_1(k1_tarski(sK0),sK1))) ) | ~spl8_3),
% 0.20/0.56    inference(resolution,[],[f109,f70])).
% 0.20/0.56  fof(f70,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f31])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f8])).
% 0.20/0.56  fof(f8,axiom,(
% 0.20/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.56  fof(f109,plain,(
% 0.20/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | ~spl8_3),
% 0.20/0.56    inference(avatar_component_clause,[],[f107])).
% 0.20/0.56  fof(f520,plain,(
% 0.20/0.56    ~spl8_10 | ~spl8_18 | spl8_1 | ~spl8_5 | ~spl8_8),
% 0.20/0.56    inference(avatar_split_clause,[],[f519,f138,f117,f97,f218,f151])).
% 0.20/0.56  fof(f151,plain,(
% 0.20/0.56    spl8_10 <=> v5_relat_1(sK2,sK1)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.20/0.56  fof(f97,plain,(
% 0.20/0.56    spl8_1 <=> r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.56  fof(f117,plain,(
% 0.20/0.56    spl8_5 <=> v1_funct_1(sK2)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.56  fof(f519,plain,(
% 0.20/0.56    ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v5_relat_1(sK2,sK1) | (spl8_1 | ~spl8_5 | ~spl8_8)),
% 0.20/0.56    inference(subsumption_resolution,[],[f518,f140])).
% 0.20/0.56  fof(f518,plain,(
% 0.20/0.56    ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v5_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | (spl8_1 | ~spl8_5)),
% 0.20/0.56    inference(subsumption_resolution,[],[f517,f119])).
% 0.20/0.56  fof(f119,plain,(
% 0.20/0.56    v1_funct_1(sK2) | ~spl8_5),
% 0.20/0.56    inference(avatar_component_clause,[],[f117])).
% 0.20/0.56  fof(f517,plain,(
% 0.20/0.56    ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v5_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | spl8_1),
% 0.20/0.56    inference(resolution,[],[f99,f69])).
% 0.20/0.56  fof(f69,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f30])).
% 0.20/0.56  fof(f30,plain,(
% 0.20/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.56    inference(flattening,[],[f29])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.56    inference(ennf_transformation,[],[f14])).
% 0.20/0.56  fof(f14,axiom,(
% 0.20/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).
% 0.20/0.56  fof(f99,plain,(
% 0.20/0.56    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | spl8_1),
% 0.20/0.56    inference(avatar_component_clause,[],[f97])).
% 0.20/0.56  fof(f516,plain,(
% 0.20/0.56    ~spl8_29),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f515])).
% 0.20/0.56  fof(f515,plain,(
% 0.20/0.56    $false | ~spl8_29),
% 0.20/0.56    inference(subsumption_resolution,[],[f510,f121])).
% 0.20/0.56  fof(f121,plain,(
% 0.20/0.56    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.20/0.56    inference(superposition,[],[f88,f80])).
% 0.20/0.56  fof(f80,plain,(
% 0.20/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f2])).
% 0.20/0.56  fof(f2,axiom,(
% 0.20/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.56  fof(f88,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v1_xboole_0(k2_tarski(X0,X1))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0,X1] : ~v1_xboole_0(k2_tarski(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).
% 0.20/0.56  fof(f510,plain,(
% 0.20/0.56    v1_xboole_0(k1_tarski(sK0)) | ~spl8_29),
% 0.20/0.56    inference(resolution,[],[f495,f124])).
% 0.20/0.56  fof(f124,plain,(
% 0.20/0.56    ( ! [X1] : (r2_hidden(sK7(X1),X1) | v1_xboole_0(X1)) )),
% 0.20/0.56    inference(resolution,[],[f71,f84])).
% 0.20/0.56  fof(f84,plain,(
% 0.20/0.56    ( ! [X0] : (m1_subset_1(sK7(X0),X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f55])).
% 0.20/0.56  fof(f55,plain,(
% 0.20/0.56    ! [X0] : m1_subset_1(sK7(X0),X0)),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f7,f54])).
% 0.20/0.56  fof(f54,plain,(
% 0.20/0.56    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK7(X0),X0))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f7,axiom,(
% 0.20/0.56    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.20/0.56  fof(f71,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f33])).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.56    inference(flattening,[],[f32])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f10])).
% 0.20/0.56  fof(f10,axiom,(
% 0.20/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.56  fof(f495,plain,(
% 0.20/0.56    ( ! [X10] : (~r2_hidden(X10,k1_tarski(sK0))) ) | ~spl8_29),
% 0.20/0.56    inference(subsumption_resolution,[],[f491,f82])).
% 0.20/0.56  % (14099)Refutation not found, incomplete strategy% (14099)------------------------------
% 0.20/0.56  % (14099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (14099)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (14099)Memory used [KB]: 11001
% 0.20/0.56  % (14099)Time elapsed: 0.146 s
% 0.20/0.56  % (14099)------------------------------
% 0.20/0.56  % (14099)------------------------------
% 1.68/0.58  fof(f82,plain,(
% 1.68/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f1])).
% 1.68/0.58  fof(f1,axiom,(
% 1.68/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.68/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.68/0.58  fof(f491,plain,(
% 1.68/0.58    ( ! [X10] : (~r2_hidden(X10,k1_tarski(sK0)) | ~r1_tarski(k1_xboole_0,k4_tarski(X10,sK3(k1_xboole_0,X10)))) ) | ~spl8_29),
% 1.68/0.58    inference(resolution,[],[f380,f68])).
% 1.68/0.58  fof(f68,plain,(
% 1.68/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f28])).
% 1.68/0.58  fof(f28,plain,(
% 1.68/0.58    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.68/0.58    inference(ennf_transformation,[],[f15])).
% 1.68/0.58  fof(f15,axiom,(
% 1.68/0.58    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.68/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.68/0.58  fof(f380,plain,(
% 1.68/0.58    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK3(k1_xboole_0,X0)),k1_xboole_0) | ~r2_hidden(X0,k1_tarski(sK0))) ) | ~spl8_29),
% 1.68/0.58    inference(subsumption_resolution,[],[f379,f81])).
% 1.68/0.58  fof(f379,plain,(
% 1.68/0.58    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(k4_tarski(X0,sK3(k1_xboole_0,X0)),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))) ) | ~spl8_29),
% 1.68/0.58    inference(trivial_inequality_removal,[],[f376])).
% 1.68/0.58  fof(f376,plain,(
% 1.68/0.58    ( ! [X0] : (k1_tarski(sK0) != k1_tarski(sK0) | ~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(k4_tarski(X0,sK3(k1_xboole_0,X0)),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))) ) | ~spl8_29),
% 1.68/0.58    inference(superposition,[],[f67,f336])).
% 1.68/0.58  fof(f336,plain,(
% 1.68/0.58    k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,k1_xboole_0) | ~spl8_29),
% 1.68/0.58    inference(avatar_component_clause,[],[f334])).
% 1.68/0.58  fof(f67,plain,(
% 1.68/0.58    ( ! [X2,X0,X3,X1] : (k1_relset_1(X1,X0,X2) != X1 | ~r2_hidden(X3,X1) | r2_hidden(k4_tarski(X3,sK3(X2,X3)),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 1.68/0.58    inference(cnf_transformation,[],[f50])).
% 1.68/0.58  fof(f50,plain,(
% 1.68/0.58    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK3(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK4(X1,X2),X6),X2) & r2_hidden(sK4(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.68/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f47,f49,f48])).
% 1.68/0.58  fof(f48,plain,(
% 1.68/0.58    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK3(X2,X3)),X2))),
% 1.68/0.58    introduced(choice_axiom,[])).
% 1.68/0.58  fof(f49,plain,(
% 1.68/0.58    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK4(X1,X2),X6),X2) & r2_hidden(sK4(X1,X2),X1)))),
% 1.68/0.58    introduced(choice_axiom,[])).
% 1.68/0.58  fof(f47,plain,(
% 1.68/0.58    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.68/0.58    inference(rectify,[],[f46])).
% 1.68/0.58  fof(f46,plain,(
% 1.68/0.58    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.68/0.58    inference(nnf_transformation,[],[f27])).
% 1.68/0.58  fof(f27,plain,(
% 1.68/0.58    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.68/0.58    inference(ennf_transformation,[],[f18])).
% 1.68/0.58  fof(f18,axiom,(
% 1.68/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 1.68/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).
% 1.68/0.58  fof(f304,plain,(
% 1.68/0.58    spl8_16 | spl8_26 | ~spl8_8 | ~spl8_12),
% 1.68/0.58    inference(avatar_split_clause,[],[f303,f167,f138,f299,f204])).
% 1.68/0.58  fof(f303,plain,(
% 1.68/0.58    sK0 = sK5(sK2) | k1_xboole_0 = sK2 | (~spl8_8 | ~spl8_12)),
% 1.68/0.58    inference(subsumption_resolution,[],[f295,f140])).
% 1.68/0.58  fof(f295,plain,(
% 1.68/0.58    sK0 = sK5(sK2) | k1_xboole_0 = sK2 | ~v1_relat_1(sK2) | ~spl8_12),
% 1.68/0.58    inference(resolution,[],[f178,f72])).
% 1.68/0.58  fof(f178,plain,(
% 1.68/0.58    ( ! [X4,X3] : (~r2_hidden(k4_tarski(X3,X4),sK2) | sK0 = X3) ) | ~spl8_12),
% 1.68/0.58    inference(resolution,[],[f168,f61])).
% 1.68/0.58  fof(f61,plain,(
% 1.68/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | X0 = X2) )),
% 1.68/0.58    inference(cnf_transformation,[],[f45])).
% 1.68/0.58  fof(f45,plain,(
% 1.68/0.58    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 1.68/0.58    inference(flattening,[],[f44])).
% 1.68/0.58  fof(f44,plain,(
% 1.68/0.58    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | (~r2_hidden(X1,X3) | X0 != X2)) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 1.68/0.58    inference(nnf_transformation,[],[f6])).
% 1.68/0.58  fof(f6,axiom,(
% 1.68/0.58    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 1.68/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).
% 1.68/0.58  fof(f168,plain,(
% 1.68/0.58    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(sK0),sK1)) | ~r2_hidden(X0,sK2)) ) | ~spl8_12),
% 1.68/0.58    inference(avatar_component_clause,[],[f167])).
% 1.68/0.58  fof(f240,plain,(
% 1.68/0.58    spl8_20 | ~spl8_4 | ~spl8_16),
% 1.68/0.58    inference(avatar_split_clause,[],[f224,f204,f112,f237])).
% 1.68/0.58  fof(f112,plain,(
% 1.68/0.58    spl8_4 <=> v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.68/0.58  fof(f224,plain,(
% 1.68/0.58    v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1) | (~spl8_4 | ~spl8_16)),
% 1.68/0.58    inference(backward_demodulation,[],[f114,f206])).
% 1.68/0.58  fof(f206,plain,(
% 1.68/0.58    k1_xboole_0 = sK2 | ~spl8_16),
% 1.68/0.58    inference(avatar_component_clause,[],[f204])).
% 1.68/0.58  fof(f114,plain,(
% 1.68/0.58    v1_funct_2(sK2,k1_tarski(sK0),sK1) | ~spl8_4),
% 1.68/0.58    inference(avatar_component_clause,[],[f112])).
% 1.68/0.58  fof(f154,plain,(
% 1.68/0.58    spl8_10 | ~spl8_3),
% 1.68/0.58    inference(avatar_split_clause,[],[f147,f107,f151])).
% 1.68/0.58  fof(f147,plain,(
% 1.68/0.58    v5_relat_1(sK2,sK1) | ~spl8_3),
% 1.68/0.58    inference(resolution,[],[f87,f109])).
% 1.68/0.58  fof(f87,plain,(
% 1.68/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f41])).
% 1.68/0.58  fof(f41,plain,(
% 1.68/0.58    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.68/0.58    inference(ennf_transformation,[],[f22])).
% 1.68/0.58  fof(f22,plain,(
% 1.68/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.68/0.58    inference(pure_predicate_removal,[],[f17])).
% 1.68/0.58  fof(f17,axiom,(
% 1.68/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.68/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.68/0.58  fof(f141,plain,(
% 1.68/0.58    spl8_8 | ~spl8_3),
% 1.68/0.58    inference(avatar_split_clause,[],[f134,f107,f138])).
% 1.68/0.58  fof(f134,plain,(
% 1.68/0.58    v1_relat_1(sK2) | ~spl8_3),
% 1.68/0.58    inference(resolution,[],[f83,f109])).
% 1.68/0.58  fof(f83,plain,(
% 1.68/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f38])).
% 1.68/0.58  fof(f38,plain,(
% 1.68/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.68/0.58    inference(ennf_transformation,[],[f16])).
% 1.68/0.58  fof(f16,axiom,(
% 1.68/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.68/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.68/0.58  fof(f120,plain,(
% 1.68/0.58    spl8_5),
% 1.68/0.58    inference(avatar_split_clause,[],[f56,f117])).
% 1.68/0.58  fof(f56,plain,(
% 1.68/0.58    v1_funct_1(sK2)),
% 1.68/0.58    inference(cnf_transformation,[],[f43])).
% 1.68/0.58  fof(f43,plain,(
% 1.68/0.58    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 1.68/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f42])).
% 1.68/0.58  fof(f42,plain,(
% 1.68/0.58    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 1.68/0.58    introduced(choice_axiom,[])).
% 1.68/0.58  fof(f24,plain,(
% 1.68/0.58    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.68/0.58    inference(flattening,[],[f23])).
% 1.68/0.58  fof(f23,plain,(
% 1.68/0.58    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.68/0.58    inference(ennf_transformation,[],[f21])).
% 1.68/0.58  fof(f21,negated_conjecture,(
% 1.68/0.58    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.68/0.58    inference(negated_conjecture,[],[f20])).
% 1.68/0.58  fof(f20,conjecture,(
% 1.68/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.68/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).
% 1.68/0.58  fof(f115,plain,(
% 1.68/0.58    spl8_4),
% 1.68/0.58    inference(avatar_split_clause,[],[f57,f112])).
% 1.68/0.58  fof(f57,plain,(
% 1.68/0.58    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 1.68/0.58    inference(cnf_transformation,[],[f43])).
% 1.68/0.58  fof(f110,plain,(
% 1.68/0.58    spl8_3),
% 1.68/0.58    inference(avatar_split_clause,[],[f58,f107])).
% 1.68/0.58  fof(f58,plain,(
% 1.68/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.68/0.58    inference(cnf_transformation,[],[f43])).
% 1.68/0.58  fof(f105,plain,(
% 1.68/0.58    ~spl8_2),
% 1.68/0.58    inference(avatar_split_clause,[],[f59,f102])).
% 1.68/0.58  fof(f59,plain,(
% 1.68/0.58    k1_xboole_0 != sK1),
% 1.68/0.58    inference(cnf_transformation,[],[f43])).
% 1.68/0.58  fof(f100,plain,(
% 1.68/0.58    ~spl8_1),
% 1.68/0.58    inference(avatar_split_clause,[],[f60,f97])).
% 1.68/0.58  fof(f60,plain,(
% 1.68/0.58    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 1.68/0.58    inference(cnf_transformation,[],[f43])).
% 1.68/0.58  % SZS output end Proof for theBenchmark
% 1.68/0.58  % (14092)------------------------------
% 1.68/0.58  % (14092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.58  % (14092)Termination reason: Refutation
% 1.68/0.58  
% 1.68/0.58  % (14092)Memory used [KB]: 6524
% 1.68/0.58  % (14092)Time elapsed: 0.164 s
% 1.68/0.58  % (14092)------------------------------
% 1.68/0.58  % (14092)------------------------------
% 1.68/0.58  % (14070)Success in time 0.226 s
%------------------------------------------------------------------------------
