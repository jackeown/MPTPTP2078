%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0993+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 112 expanded)
%              Number of leaves         :   17 (  48 expanded)
%              Depth                    :    7
%              Number of atoms          :  187 ( 359 expanded)
%              Number of equality atoms :   20 (  30 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f32,f37,f47,f51,f55,f59,f64,f69,f74,f80,f86,f89])).

fof(f89,plain,
    ( ~ spl4_2
    | spl4_12
    | ~ spl4_13 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | ~ spl4_2
    | spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f87,f31])).

fof(f31,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl4_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f87,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl4_12
    | ~ spl4_13 ),
    inference(resolution,[],[f85,f79])).

fof(f79,plain,
    ( ~ r2_relset_1(sK0,sK1,k7_relat_1(sK3,sK2),sK3)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl4_12
  <=> r2_relset_1(sK0,sK1,k7_relat_1(sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f85,plain,
    ( ! [X0] :
        ( r2_relset_1(sK0,sK1,k7_relat_1(sK3,X0),sK3)
        | ~ r1_tarski(sK0,X0) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl4_13
  <=> ! [X0] :
        ( r2_relset_1(sK0,sK1,k7_relat_1(sK3,X0),sK3)
        | ~ r1_tarski(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f86,plain,
    ( spl4_13
    | ~ spl4_3
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f82,f62,f53,f34,f84])).

fof(f34,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f53,plain,
    ( spl4_7
  <=> ! [X1,X3,X0,X2] :
        ( r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
        | ~ r1_tarski(X1,X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f62,plain,
    ( spl4_9
  <=> ! [X0] : k7_relat_1(sK3,X0) = k5_relset_1(sK0,sK1,sK3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f82,plain,
    ( ! [X0] :
        ( r2_relset_1(sK0,sK1,k7_relat_1(sK3,X0),sK3)
        | ~ r1_tarski(sK0,X0) )
    | ~ spl4_3
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f81,f63])).

fof(f63,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k5_relset_1(sK0,sK1,sK3,X0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f62])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | r2_relset_1(sK0,sK1,k5_relset_1(sK0,sK1,sK3,X0),sK3) )
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(resolution,[],[f54,f36])).

fof(f36,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f54,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ r1_tarski(X1,X2)
        | r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f53])).

fof(f80,plain,
    ( ~ spl4_12
    | spl4_1
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f75,f72,f24,f77])).

fof(f24,plain,
    ( spl4_1
  <=> r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f72,plain,
    ( spl4_11
  <=> ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f75,plain,
    ( ~ r2_relset_1(sK0,sK1,k7_relat_1(sK3,sK2),sK3)
    | spl4_1
    | ~ spl4_11 ),
    inference(superposition,[],[f26,f73])).

fof(f73,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f72])).

fof(f26,plain,
    ( ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f74,plain,
    ( spl4_11
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f70,f67,f34,f72])).

fof(f67,plain,
    ( spl4_10
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f70,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(resolution,[],[f68,f36])).

fof(f68,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f69,plain,
    ( spl4_10
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f65,f57,f44,f67])).

fof(f44,plain,
    ( spl4_5
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f57,plain,
    ( spl4_8
  <=> ! [X1,X3,X0,X2] :
        ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f65,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) )
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(resolution,[],[f58,f46])).

fof(f46,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f58,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f64,plain,
    ( spl4_9
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f60,f49,f34,f62])).

fof(f49,plain,
    ( spl4_6
  <=> ! [X1,X3,X0,X2] :
        ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f60,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k5_relset_1(sK0,sK1,sK3,X0)
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(resolution,[],[f50,f36])).

fof(f50,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f49])).

fof(f59,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f22,f57])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f55,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f21,f53])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

fof(f51,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f20,f49])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f47,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f15,f44])).

fof(f15,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3)
    & r1_tarski(sK0,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
        & r1_tarski(X0,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3)
      & r1_tarski(sK0,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X0,X2)
         => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X0,X2)
       => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).

fof(f37,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f17,f34])).

fof(f17,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f18,f29])).

fof(f18,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f27,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f19,f24])).

fof(f19,plain,(
    ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f14])).

%------------------------------------------------------------------------------
