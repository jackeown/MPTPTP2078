%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:39 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 227 expanded)
%              Number of leaves         :   14 (  57 expanded)
%              Depth                    :   17
%              Number of atoms          :  233 (1072 expanded)
%              Number of equality atoms :   72 ( 442 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f78,f95,f109,f130])).

fof(f130,plain,
    ( ~ spl4_2
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(trivial_inequality_removal,[],[f128])).

fof(f128,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(superposition,[],[f103,f112])).

fof(f112,plain,
    ( ! [X0] : k1_xboole_0 = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,X0)
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f111,f54])).

fof(f54,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f111,plain,
    ( ! [X0] : k1_xboole_0 = k8_relset_1(sK0,k1_xboole_0,sK2,X0)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f73,f98])).

fof(f98,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f97,f31])).

fof(f31,plain,(
    sK0 != k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( sK0 != k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0))
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( sK0 != k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0))
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_2)).

fof(f97,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) ),
    inference(subsumption_resolution,[],[f96,f27])).

fof(f27,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f96,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_funct_1(sK2)
    | sK0 = k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) ),
    inference(subsumption_resolution,[],[f89,f28])).

fof(f28,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f89,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | sK0 = k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) ),
    inference(resolution,[],[f88,f29])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_xboole_0 = X0
      | ~ v1_funct_2(X2,X1,X0)
      | ~ v1_funct_1(X2)
      | k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f87,f43])).

fof(f43,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X1,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X1,X0)
      | ~ v1_funct_1(X2)
      | k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = X1 ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X1,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_1(X2)
      | k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(resolution,[],[f40,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X1,k8_relset_1(X1,X2,X0,X3))
      | ~ v1_funct_1(X0)
      | k8_relset_1(X1,X2,X0,X3) = X1
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f42,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
     => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_2)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_2)).

fof(f73,plain,
    ( ! [X0] : k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,X0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl4_5
  <=> ! [X0] : k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f103,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k7_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f102,f54])).

fof(f102,plain,(
    sK0 != k8_relset_1(sK0,k1_xboole_0,sK2,k7_relset_1(sK0,k1_xboole_0,sK2,sK0)) ),
    inference(backward_demodulation,[],[f31,f98])).

fof(f109,plain,
    ( ~ spl4_2
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | ~ spl4_2
    | spl4_6 ),
    inference(subsumption_resolution,[],[f107,f32])).

fof(f32,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f107,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_2
    | spl4_6 ),
    inference(backward_demodulation,[],[f77,f54])).

fof(f77,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl4_6
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f95,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f93,f31])).

fof(f93,plain,
    ( sK0 = k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f92,f27])).

fof(f92,plain,
    ( ~ v1_funct_1(sK2)
    | sK0 = k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f91,f28])).

fof(f91,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | sK0 = k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f89,f50])).

fof(f50,plain,
    ( k1_xboole_0 != sK1
    | spl4_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl4_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f78,plain,
    ( spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f69,f75,f72])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK0)
      | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,X0) ) ),
    inference(resolution,[],[f68,f29])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_xboole_0(X0)
      | k1_xboole_0 = k8_relset_1(X0,X2,X1,X3) ) ),
    inference(resolution,[],[f66,f34])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k8_relset_1(X1,X2,X0,X4))
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f39,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f55,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f30,f52,f48])).

fof(f30,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:02:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.37  ipcrm: permission denied for id (1212841984)
% 0.21/0.38  ipcrm: permission denied for id (1212973064)
% 0.21/0.39  ipcrm: permission denied for id (1213005839)
% 0.21/0.39  ipcrm: permission denied for id (1213038613)
% 0.21/0.40  ipcrm: permission denied for id (1213071383)
% 0.21/0.40  ipcrm: permission denied for id (1213104155)
% 0.21/0.41  ipcrm: permission denied for id (1213202465)
% 0.21/0.41  ipcrm: permission denied for id (1213235236)
% 0.21/0.42  ipcrm: permission denied for id (1213333545)
% 0.21/0.42  ipcrm: permission denied for id (1213399082)
% 0.21/0.43  ipcrm: permission denied for id (1213431861)
% 0.21/0.44  ipcrm: permission denied for id (1213562941)
% 0.21/0.46  ipcrm: permission denied for id (1213661256)
% 0.21/0.46  ipcrm: permission denied for id (1213694025)
% 0.21/0.47  ipcrm: permission denied for id (1213759568)
% 0.21/0.48  ipcrm: permission denied for id (1213825113)
% 0.21/0.48  ipcrm: permission denied for id (1213857886)
% 0.21/0.49  ipcrm: permission denied for id (1213923426)
% 0.21/0.49  ipcrm: permission denied for id (1213956197)
% 0.21/0.50  ipcrm: permission denied for id (1214120047)
% 0.21/0.51  ipcrm: permission denied for id (1214251126)
% 0.21/0.52  ipcrm: permission denied for id (1214316670)
% 1.05/0.65  % (12976)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.05/0.66  % (12978)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.05/0.66  % (12995)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.05/0.66  % (12985)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.05/0.66  % (12984)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.05/0.67  % (12991)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.05/0.67  % (12969)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.05/0.67  % (12995)Refutation found. Thanks to Tanya!
% 1.05/0.67  % SZS status Theorem for theBenchmark
% 1.05/0.67  % SZS output start Proof for theBenchmark
% 1.05/0.67  fof(f131,plain,(
% 1.05/0.67    $false),
% 1.05/0.67    inference(avatar_sat_refutation,[],[f55,f78,f95,f109,f130])).
% 1.05/0.67  fof(f130,plain,(
% 1.05/0.67    ~spl4_2 | ~spl4_5),
% 1.05/0.67    inference(avatar_contradiction_clause,[],[f129])).
% 1.05/0.67  fof(f129,plain,(
% 1.05/0.67    $false | (~spl4_2 | ~spl4_5)),
% 1.05/0.67    inference(trivial_inequality_removal,[],[f128])).
% 1.05/0.67  fof(f128,plain,(
% 1.05/0.67    k1_xboole_0 != k1_xboole_0 | (~spl4_2 | ~spl4_5)),
% 1.05/0.67    inference(superposition,[],[f103,f112])).
% 1.05/0.67  fof(f112,plain,(
% 1.05/0.67    ( ! [X0] : (k1_xboole_0 = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,X0)) ) | (~spl4_2 | ~spl4_5)),
% 1.05/0.67    inference(forward_demodulation,[],[f111,f54])).
% 1.05/0.67  fof(f54,plain,(
% 1.05/0.67    k1_xboole_0 = sK0 | ~spl4_2),
% 1.05/0.67    inference(avatar_component_clause,[],[f52])).
% 1.05/0.67  fof(f52,plain,(
% 1.05/0.67    spl4_2 <=> k1_xboole_0 = sK0),
% 1.05/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.05/0.67  fof(f111,plain,(
% 1.05/0.67    ( ! [X0] : (k1_xboole_0 = k8_relset_1(sK0,k1_xboole_0,sK2,X0)) ) | ~spl4_5),
% 1.05/0.67    inference(forward_demodulation,[],[f73,f98])).
% 1.05/0.67  fof(f98,plain,(
% 1.05/0.67    k1_xboole_0 = sK1),
% 1.05/0.67    inference(subsumption_resolution,[],[f97,f31])).
% 1.05/0.67  fof(f31,plain,(
% 1.05/0.67    sK0 != k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0))),
% 1.05/0.67    inference(cnf_transformation,[],[f22])).
% 1.05/0.67  fof(f22,plain,(
% 1.05/0.67    sK0 != k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.05/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f21])).
% 1.05/0.67  fof(f21,plain,(
% 1.05/0.67    ? [X0,X1,X2] : (k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (sK0 != k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.05/0.67    introduced(choice_axiom,[])).
% 1.05/0.67  fof(f12,plain,(
% 1.05/0.67    ? [X0,X1,X2] : (k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.05/0.67    inference(flattening,[],[f11])).
% 1.05/0.67  fof(f11,plain,(
% 1.05/0.67    ? [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.05/0.67    inference(ennf_transformation,[],[f10])).
% 1.05/0.67  fof(f10,negated_conjecture,(
% 1.05/0.67    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0))),
% 1.05/0.67    inference(negated_conjecture,[],[f9])).
% 1.05/0.67  fof(f9,conjecture,(
% 1.05/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0))),
% 1.05/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_2)).
% 1.05/0.67  fof(f97,plain,(
% 1.05/0.67    k1_xboole_0 = sK1 | sK0 = k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0))),
% 1.05/0.67    inference(subsumption_resolution,[],[f96,f27])).
% 1.05/0.67  fof(f27,plain,(
% 1.05/0.67    v1_funct_1(sK2)),
% 1.05/0.67    inference(cnf_transformation,[],[f22])).
% 1.05/0.67  fof(f96,plain,(
% 1.05/0.67    k1_xboole_0 = sK1 | ~v1_funct_1(sK2) | sK0 = k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0))),
% 1.05/0.67    inference(subsumption_resolution,[],[f89,f28])).
% 1.05/0.67  fof(f28,plain,(
% 1.05/0.67    v1_funct_2(sK2,sK0,sK1)),
% 1.05/0.67    inference(cnf_transformation,[],[f22])).
% 1.05/0.67  fof(f89,plain,(
% 1.05/0.67    k1_xboole_0 = sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | sK0 = k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0))),
% 1.05/0.67    inference(resolution,[],[f88,f29])).
% 1.05/0.67  fof(f29,plain,(
% 1.05/0.67    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.05/0.67    inference(cnf_transformation,[],[f22])).
% 1.05/0.67  fof(f88,plain,(
% 1.05/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_xboole_0 = X0 | ~v1_funct_2(X2,X1,X0) | ~v1_funct_1(X2) | k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = X1) )),
% 1.05/0.67    inference(subsumption_resolution,[],[f87,f43])).
% 1.05/0.67  fof(f43,plain,(
% 1.05/0.67    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.05/0.67    inference(equality_resolution,[],[f36])).
% 1.05/0.67  fof(f36,plain,(
% 1.05/0.67    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.05/0.67    inference(cnf_transformation,[],[f26])).
% 1.05/0.67  fof(f26,plain,(
% 1.05/0.67    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.05/0.67    inference(flattening,[],[f25])).
% 1.05/0.67  fof(f25,plain,(
% 1.05/0.67    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.05/0.67    inference(nnf_transformation,[],[f4])).
% 1.05/0.67  fof(f4,axiom,(
% 1.05/0.67    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.05/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.05/0.67  fof(f87,plain,(
% 1.05/0.67    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X1,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X1,X0) | ~v1_funct_1(X2) | k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = X1) )),
% 1.05/0.67    inference(duplicate_literal_removal,[],[f85])).
% 1.05/0.67  fof(f85,plain,(
% 1.05/0.67    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X1,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X1,X0) | ~v1_funct_1(X2) | ~v1_funct_1(X2) | k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 1.05/0.67    inference(resolution,[],[f40,f67])).
% 1.05/0.67  fof(f67,plain,(
% 1.05/0.67    ( ! [X2,X0,X3,X1] : (~r1_tarski(X1,k8_relset_1(X1,X2,X0,X3)) | ~v1_funct_1(X0) | k8_relset_1(X1,X2,X0,X3) = X1 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.05/0.67    inference(resolution,[],[f42,f37])).
% 1.05/0.67  fof(f37,plain,(
% 1.05/0.67    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.05/0.67    inference(cnf_transformation,[],[f26])).
% 1.05/0.67  fof(f42,plain,(
% 1.05/0.67    ( ! [X2,X0,X3,X1] : (r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) )),
% 1.05/0.67    inference(cnf_transformation,[],[f20])).
% 1.05/0.67  fof(f20,plain,(
% 1.05/0.67    ! [X0,X1,X2,X3] : (r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))),
% 1.05/0.67    inference(flattening,[],[f19])).
% 1.05/0.67  fof(f19,plain,(
% 1.05/0.67    ! [X0,X1,X2,X3] : (r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)))),
% 1.05/0.67    inference(ennf_transformation,[],[f7])).
% 1.05/0.67  fof(f7,axiom,(
% 1.05/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0))),
% 1.05/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_2)).
% 1.05/0.67  fof(f40,plain,(
% 1.05/0.67    ( ! [X2,X0,X3,X1] : (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | k1_xboole_0 = X1 | ~r1_tarski(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.05/0.67    inference(cnf_transformation,[],[f18])).
% 1.05/0.67  fof(f18,plain,(
% 1.05/0.67    ! [X0,X1,X2,X3] : (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.05/0.67    inference(flattening,[],[f17])).
% 1.05/0.67  fof(f17,plain,(
% 1.05/0.67    ! [X0,X1,X2,X3] : (((r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.05/0.67    inference(ennf_transformation,[],[f8])).
% 1.05/0.67  fof(f8,axiom,(
% 1.05/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.05/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_2)).
% 1.05/0.67  fof(f73,plain,(
% 1.05/0.67    ( ! [X0] : (k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,X0)) ) | ~spl4_5),
% 1.05/0.67    inference(avatar_component_clause,[],[f72])).
% 1.05/0.67  fof(f72,plain,(
% 1.05/0.67    spl4_5 <=> ! [X0] : k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,X0)),
% 1.05/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.05/0.67  fof(f103,plain,(
% 1.05/0.67    k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k7_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)) | ~spl4_2),
% 1.05/0.67    inference(backward_demodulation,[],[f102,f54])).
% 1.05/0.67  fof(f102,plain,(
% 1.05/0.67    sK0 != k8_relset_1(sK0,k1_xboole_0,sK2,k7_relset_1(sK0,k1_xboole_0,sK2,sK0))),
% 1.05/0.67    inference(backward_demodulation,[],[f31,f98])).
% 1.05/0.67  fof(f109,plain,(
% 1.05/0.67    ~spl4_2 | spl4_6),
% 1.05/0.67    inference(avatar_contradiction_clause,[],[f108])).
% 1.05/0.67  fof(f108,plain,(
% 1.05/0.67    $false | (~spl4_2 | spl4_6)),
% 1.05/0.67    inference(subsumption_resolution,[],[f107,f32])).
% 1.05/0.67  fof(f32,plain,(
% 1.05/0.67    v1_xboole_0(k1_xboole_0)),
% 1.05/0.67    inference(cnf_transformation,[],[f1])).
% 1.05/0.67  fof(f1,axiom,(
% 1.05/0.67    v1_xboole_0(k1_xboole_0)),
% 1.05/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.05/0.67  fof(f107,plain,(
% 1.05/0.67    ~v1_xboole_0(k1_xboole_0) | (~spl4_2 | spl4_6)),
% 1.05/0.67    inference(backward_demodulation,[],[f77,f54])).
% 1.05/0.67  fof(f77,plain,(
% 1.05/0.67    ~v1_xboole_0(sK0) | spl4_6),
% 1.05/0.67    inference(avatar_component_clause,[],[f75])).
% 1.05/0.67  fof(f75,plain,(
% 1.05/0.67    spl4_6 <=> v1_xboole_0(sK0)),
% 1.05/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.05/0.67  fof(f95,plain,(
% 1.05/0.67    spl4_1),
% 1.05/0.67    inference(avatar_contradiction_clause,[],[f94])).
% 1.05/0.67  fof(f94,plain,(
% 1.05/0.67    $false | spl4_1),
% 1.05/0.67    inference(subsumption_resolution,[],[f93,f31])).
% 1.05/0.67  fof(f93,plain,(
% 1.05/0.67    sK0 = k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) | spl4_1),
% 1.05/0.67    inference(subsumption_resolution,[],[f92,f27])).
% 1.05/0.67  fof(f92,plain,(
% 1.05/0.67    ~v1_funct_1(sK2) | sK0 = k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) | spl4_1),
% 1.05/0.67    inference(subsumption_resolution,[],[f91,f28])).
% 1.05/0.67  fof(f91,plain,(
% 1.05/0.67    ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | sK0 = k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) | spl4_1),
% 1.05/0.67    inference(subsumption_resolution,[],[f89,f50])).
% 1.05/0.67  fof(f50,plain,(
% 1.05/0.67    k1_xboole_0 != sK1 | spl4_1),
% 1.05/0.67    inference(avatar_component_clause,[],[f48])).
% 1.05/0.67  fof(f48,plain,(
% 1.05/0.67    spl4_1 <=> k1_xboole_0 = sK1),
% 1.05/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.05/0.67  fof(f78,plain,(
% 1.05/0.67    spl4_5 | ~spl4_6),
% 1.05/0.67    inference(avatar_split_clause,[],[f69,f75,f72])).
% 1.05/0.67  fof(f69,plain,(
% 1.05/0.67    ( ! [X0] : (~v1_xboole_0(sK0) | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,X0)) )),
% 1.05/0.67    inference(resolution,[],[f68,f29])).
% 1.05/0.67  fof(f68,plain,(
% 1.05/0.67    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_xboole_0(X0) | k1_xboole_0 = k8_relset_1(X0,X2,X1,X3)) )),
% 1.05/0.67    inference(resolution,[],[f66,f34])).
% 1.05/0.67  fof(f34,plain,(
% 1.05/0.67    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.05/0.67    inference(cnf_transformation,[],[f24])).
% 1.05/0.67  fof(f24,plain,(
% 1.05/0.67    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.05/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f23])).
% 1.05/0.67  fof(f23,plain,(
% 1.05/0.67    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.05/0.67    introduced(choice_axiom,[])).
% 1.05/0.67  fof(f14,plain,(
% 1.05/0.67    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.05/0.67    inference(ennf_transformation,[],[f3])).
% 1.05/0.67  fof(f3,axiom,(
% 1.05/0.67    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.05/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.05/0.67  fof(f66,plain,(
% 1.05/0.67    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X3,k8_relset_1(X1,X2,X0,X4)) | ~v1_xboole_0(X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.05/0.67    inference(resolution,[],[f39,f38])).
% 1.05/0.67  fof(f38,plain,(
% 1.05/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 1.05/0.67    inference(cnf_transformation,[],[f15])).
% 1.05/0.67  fof(f15,plain,(
% 1.05/0.67    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.05/0.67    inference(ennf_transformation,[],[f5])).
% 1.05/0.67  fof(f5,axiom,(
% 1.05/0.67    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.05/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.05/0.67  fof(f39,plain,(
% 1.05/0.67    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.05/0.67    inference(cnf_transformation,[],[f16])).
% 1.05/0.67  fof(f16,plain,(
% 1.05/0.67    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.05/0.67    inference(ennf_transformation,[],[f6])).
% 1.05/0.67  fof(f6,axiom,(
% 1.05/0.67    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 1.05/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 1.05/0.67  fof(f55,plain,(
% 1.05/0.67    ~spl4_1 | spl4_2),
% 1.05/0.67    inference(avatar_split_clause,[],[f30,f52,f48])).
% 1.05/0.67  fof(f30,plain,(
% 1.05/0.67    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 1.05/0.67    inference(cnf_transformation,[],[f22])).
% 1.05/0.67  % SZS output end Proof for theBenchmark
% 1.05/0.67  % (12995)------------------------------
% 1.05/0.67  % (12995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.05/0.67  % (12995)Termination reason: Refutation
% 1.05/0.67  
% 1.05/0.67  % (12995)Memory used [KB]: 10746
% 1.05/0.67  % (12995)Time elapsed: 0.071 s
% 1.05/0.67  % (12995)------------------------------
% 1.05/0.67  % (12995)------------------------------
% 1.05/0.68  % (12823)Success in time 0.314 s
%------------------------------------------------------------------------------
