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
% DateTime   : Thu Dec  3 13:03:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 455 expanded)
%              Number of leaves         :   16 ( 111 expanded)
%              Depth                    :   21
%              Number of atoms          :  327 (1422 expanded)
%              Number of equality atoms :   98 ( 589 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f402,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f94,f302,f400])).

fof(f400,plain,
    ( ~ spl4_1
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f399])).

fof(f399,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f396,f91])).

fof(f91,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_1
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f396,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(duplicate_literal_removal,[],[f394])).

fof(f394,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(resolution,[],[f371,f224])).

fof(f224,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(X0,X1,X2)
        | ~ v1_xboole_0(X1)
        | ~ v1_xboole_0(X0) )
    | ~ spl4_1 ),
    inference(superposition,[],[f203,f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f203,plain,
    ( ! [X2,X1] :
        ( v1_funct_2(k1_xboole_0,X1,X2)
        | ~ v1_xboole_0(X1) )
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f172,f186])).

fof(f186,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f181,f91])).

fof(f181,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f104,f63])).

fof(f63,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f35,f57])).

fof(f57,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f29])).

% (15053)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    & v1_funct_2(sK2,k1_xboole_0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
   => ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
      & v1_funct_2(sK2,k1_xboole_0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(global_subsumption,[],[f39,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f38,f38])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f172,plain,
    ( ! [X2,X1] :
        ( v1_funct_2(sK2,X1,X2)
        | ~ v1_xboole_0(X1) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f170,f140])).

fof(f140,plain,
    ( ! [X0] :
        ( v1_partfun1(sK2,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f137,f91])).

fof(f137,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(X0)
      | v1_partfun1(sK2,X0) ) ),
    inference(superposition,[],[f95,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0)
      | v1_partfun1(sK2,X0) ) ),
    inference(resolution,[],[f40,f71])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f63,f38])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f170,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_funct_2(sK2,X1,X2)
      | ~ v1_partfun1(sK2,X1) ) ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_funct_2(sK2,X1,X2)
      | ~ v1_partfun1(sK2,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(superposition,[],[f114,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f57,f38])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_funct_2(sK2,X0,X1)
      | ~ v1_partfun1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f110,f33])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(sK2,X0)
      | ~ v1_funct_1(sK2)
      | v1_funct_2(sK2,X0,X1)
      | ~ v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    inference(resolution,[],[f53,f71])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f371,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f370,f37])).

fof(f37,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f370,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f355,f91])).

fof(f355,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(superposition,[],[f311,f248])).

fof(f248,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_2(X1,k1_xboole_0,X0) ) ),
    inference(duplicate_literal_removal,[],[f247])).

fof(f247,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k10_relat_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_2(X1,k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f240,f57])).

fof(f240,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_2(X1,k1_xboole_0,X0) ) ),
    inference(superposition,[],[f129,f67])).

fof(f67,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f62,f57])).

fof(f62,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f22])).

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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f45,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f311,plain,
    ( ~ v1_xboole_0(k10_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f231,f286])).

fof(f286,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl4_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f231,plain,
    ( ~ v1_xboole_0(k10_relat_1(k1_xboole_0,sK1))
    | ~ spl4_1 ),
    inference(equality_resolution,[],[f209])).

fof(f209,plain,
    ( ! [X0] :
        ( k10_relat_1(k1_xboole_0,sK1) != X0
        | ~ v1_xboole_0(X0) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f208,f37])).

fof(f208,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
        | k10_relat_1(k1_xboole_0,sK1) != X0
        | ~ v1_xboole_0(X0) )
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f199,f186])).

fof(f199,plain,
    ( ! [X0] :
        ( k10_relat_1(k1_xboole_0,sK1) != X0
        | ~ v1_xboole_0(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) )
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f134,f186])).

fof(f134,plain,(
    ! [X0] :
      ( k10_relat_1(sK2,sK1) != X0
      | ~ v1_xboole_0(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) ) ),
    inference(superposition,[],[f70,f54])).

fof(f70,plain,(
    ! [X0] :
      ( k8_relset_1(X0,sK0,sK2,sK1) != X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f36,f38])).

fof(f36,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f302,plain,
    ( spl4_6
    | spl4_3
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f301,f81,f88,f285])).

fof(f88,plain,
    ( spl4_3
  <=> ! [X0] : ~ v1_xboole_0(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f301,plain,
    ( ! [X7] :
        ( ~ v1_xboole_0(X7)
        | k1_xboole_0 = sK1 )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f300,f203])).

fof(f300,plain,
    ( ! [X7] :
        ( ~ v1_xboole_0(X7)
        | k1_xboole_0 = sK1
        | ~ v1_funct_2(k1_xboole_0,X7,sK1) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f281,f91])).

fof(f281,plain,
    ( ! [X7] :
        ( ~ v1_xboole_0(X7)
        | ~ v1_xboole_0(k1_xboole_0)
        | k1_xboole_0 = sK1
        | ~ v1_funct_2(k1_xboole_0,X7,sK1) )
    | ~ spl4_1 ),
    inference(superposition,[],[f239,f249])).

fof(f249,plain,(
    ! [X2,X3] :
      ( k10_relat_1(k1_xboole_0,X3) = X2
      | k1_xboole_0 = X3
      | ~ v1_funct_2(k1_xboole_0,X2,X3) ) ),
    inference(subsumption_resolution,[],[f241,f37])).

fof(f241,plain,(
    ! [X2,X3] :
      ( k10_relat_1(k1_xboole_0,X3) = X2
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = X3
      | ~ v1_funct_2(k1_xboole_0,X2,X3) ) ),
    inference(superposition,[],[f129,f131])).

fof(f131,plain,(
    ! [X2,X3] :
      ( k1_relset_1(X2,X3,k1_xboole_0) = X2
      | k1_xboole_0 = X3
      | ~ v1_funct_2(k1_xboole_0,X2,X3) ) ),
    inference(resolution,[],[f46,f37])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k10_relat_1(X0,sK1))
        | ~ v1_xboole_0(X0) )
    | ~ spl4_1 ),
    inference(superposition,[],[f231,f38])).

fof(f94,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | ~ spl4_3 ),
    inference(resolution,[],[f89,f55])).

fof(f55,plain,(
    v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f2,f31])).

fof(f31,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK3) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f89,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f92,plain,
    ( spl4_3
    | spl4_1 ),
    inference(avatar_split_clause,[],[f78,f81,f88])).

fof(f78,plain,(
    ! [X1] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f39,f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:27:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (15066)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.45  % (15066)Refutation not found, incomplete strategy% (15066)------------------------------
% 0.21/0.45  % (15066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (15066)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (15066)Memory used [KB]: 10618
% 0.21/0.45  % (15066)Time elapsed: 0.038 s
% 0.21/0.45  % (15066)------------------------------
% 0.21/0.45  % (15066)------------------------------
% 0.21/0.47  % (15058)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (15048)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (15052)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (15048)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f402,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f92,f94,f302,f400])).
% 0.21/0.47  fof(f400,plain,(
% 0.21/0.47    ~spl4_1 | ~spl4_6),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f399])).
% 0.21/0.47  fof(f399,plain,(
% 0.21/0.47    $false | (~spl4_1 | ~spl4_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f396,f91])).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0) | ~spl4_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f81])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    spl4_1 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.47  fof(f396,plain,(
% 0.21/0.47    ~v1_xboole_0(k1_xboole_0) | (~spl4_1 | ~spl4_6)),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f394])).
% 0.21/0.47  fof(f394,plain,(
% 0.21/0.47    ~v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_xboole_0) | (~spl4_1 | ~spl4_6)),
% 0.21/0.47    inference(resolution,[],[f371,f224])).
% 0.21/0.47  fof(f224,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v1_funct_2(X0,X1,X2) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) ) | ~spl4_1),
% 0.21/0.47    inference(superposition,[],[f203,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.47  fof(f203,plain,(
% 0.21/0.47    ( ! [X2,X1] : (v1_funct_2(k1_xboole_0,X1,X2) | ~v1_xboole_0(X1)) ) | ~spl4_1),
% 0.21/0.47    inference(backward_demodulation,[],[f172,f186])).
% 0.21/0.47  fof(f186,plain,(
% 0.21/0.47    k1_xboole_0 = sK2 | ~spl4_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f181,f91])).
% 0.21/0.47  fof(f181,plain,(
% 0.21/0.47    k1_xboole_0 = sK2 | ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    inference(resolution,[],[f104,f63])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.47    inference(backward_demodulation,[],[f35,f57])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.47    inference(equality_resolution,[],[f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f29])).
% 0.21/0.47  % (15053)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.47    inference(flattening,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.47    inference(nnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_2(sK2,k1_xboole_0,sK0) & v1_funct_1(sK2)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => (k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_2(sK2,k1_xboole_0,sK0) & v1_funct_1(sK2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2))),
% 0.21/0.47    inference(flattening,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.21/0.47    inference(negated_conjecture,[],[f12])).
% 0.21/0.47  fof(f12,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.21/0.47    inference(global_subsumption,[],[f39,f68])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    ( ! [X0,X1] : (X0 = X1 | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.21/0.47    inference(superposition,[],[f38,f38])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.47  fof(f172,plain,(
% 0.21/0.47    ( ! [X2,X1] : (v1_funct_2(sK2,X1,X2) | ~v1_xboole_0(X1)) ) | ~spl4_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f170,f140])).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    ( ! [X0] : (v1_partfun1(sK2,X0) | ~v1_xboole_0(X0)) ) | ~spl4_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f137,f91])).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(X0) | v1_partfun1(sK2,X0)) )),
% 0.21/0.47    inference(superposition,[],[f95,f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f29])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0) | v1_partfun1(sK2,X0)) )),
% 0.21/0.47    inference(resolution,[],[f40,f71])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.47    inference(superposition,[],[f63,f38])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).
% 0.21/0.47  fof(f170,plain,(
% 0.21/0.47    ( ! [X2,X1] : (~v1_xboole_0(X1) | v1_funct_2(sK2,X1,X2) | ~v1_partfun1(sK2,X1)) )),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f166])).
% 0.21/0.47  fof(f166,plain,(
% 0.21/0.47    ( ! [X2,X1] : (~v1_xboole_0(X1) | v1_funct_2(sK2,X1,X2) | ~v1_partfun1(sK2,X1) | ~v1_xboole_0(X1)) )),
% 0.21/0.47    inference(superposition,[],[f114,f74])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.47    inference(superposition,[],[f57,f38])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1)) | v1_funct_2(sK2,X0,X1) | ~v1_partfun1(sK2,X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f110,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    v1_funct_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_partfun1(sK2,X0) | ~v1_funct_1(sK2) | v1_funct_2(sK2,X0,X1) | ~v1_xboole_0(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.47    inference(resolution,[],[f53,f71])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(flattening,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).
% 0.21/0.47  fof(f371,plain,(
% 0.21/0.47    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_1 | ~spl4_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f370,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.47  fof(f370,plain,(
% 0.21/0.47    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_1 | ~spl4_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f355,f91])).
% 0.21/0.47  fof(f355,plain,(
% 0.21/0.47    ~v1_xboole_0(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_1 | ~spl4_6)),
% 0.21/0.48    inference(superposition,[],[f311,f248])).
% 0.21/0.48  fof(f248,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X1,k1_xboole_0,X0)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f247])).
% 0.21/0.48  fof(f247,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k10_relat_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X1,k1_xboole_0,X0)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f240,f57])).
% 0.21/0.48  fof(f240,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X1,k1_xboole_0,X0)) )),
% 0.21/0.48    inference(superposition,[],[f129,f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f62,f57])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.48    inference(equality_resolution,[],[f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(nnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f126])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(superposition,[],[f45,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.21/0.48  fof(f311,plain,(
% 0.21/0.48    ~v1_xboole_0(k10_relat_1(k1_xboole_0,k1_xboole_0)) | (~spl4_1 | ~spl4_6)),
% 0.21/0.48    inference(backward_demodulation,[],[f231,f286])).
% 0.21/0.48  fof(f286,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | ~spl4_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f285])).
% 0.21/0.48  fof(f285,plain,(
% 0.21/0.48    spl4_6 <=> k1_xboole_0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.48  fof(f231,plain,(
% 0.21/0.48    ~v1_xboole_0(k10_relat_1(k1_xboole_0,sK1)) | ~spl4_1),
% 0.21/0.48    inference(equality_resolution,[],[f209])).
% 0.21/0.48  fof(f209,plain,(
% 0.21/0.48    ( ! [X0] : (k10_relat_1(k1_xboole_0,sK1) != X0 | ~v1_xboole_0(X0)) ) | ~spl4_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f208,f37])).
% 0.21/0.48  fof(f208,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | k10_relat_1(k1_xboole_0,sK1) != X0 | ~v1_xboole_0(X0)) ) | ~spl4_1),
% 0.21/0.48    inference(forward_demodulation,[],[f199,f186])).
% 0.21/0.48  fof(f199,plain,(
% 0.21/0.48    ( ! [X0] : (k10_relat_1(k1_xboole_0,sK1) != X0 | ~v1_xboole_0(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) ) | ~spl4_1),
% 0.21/0.48    inference(backward_demodulation,[],[f134,f186])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    ( ! [X0] : (k10_relat_1(sK2,sK1) != X0 | ~v1_xboole_0(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) )),
% 0.21/0.48    inference(superposition,[],[f70,f54])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X0] : (k8_relset_1(X0,sK0,sK2,sK1) != X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(superposition,[],[f36,f38])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f302,plain,(
% 0.21/0.48    spl4_6 | spl4_3 | ~spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f301,f81,f88,f285])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    spl4_3 <=> ! [X0] : ~v1_xboole_0(X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.48  fof(f301,plain,(
% 0.21/0.48    ( ! [X7] : (~v1_xboole_0(X7) | k1_xboole_0 = sK1) ) | ~spl4_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f300,f203])).
% 0.21/0.48  fof(f300,plain,(
% 0.21/0.48    ( ! [X7] : (~v1_xboole_0(X7) | k1_xboole_0 = sK1 | ~v1_funct_2(k1_xboole_0,X7,sK1)) ) | ~spl4_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f281,f91])).
% 0.21/0.48  fof(f281,plain,(
% 0.21/0.48    ( ! [X7] : (~v1_xboole_0(X7) | ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK1 | ~v1_funct_2(k1_xboole_0,X7,sK1)) ) | ~spl4_1),
% 0.21/0.48    inference(superposition,[],[f239,f249])).
% 0.21/0.48  fof(f249,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k10_relat_1(k1_xboole_0,X3) = X2 | k1_xboole_0 = X3 | ~v1_funct_2(k1_xboole_0,X2,X3)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f241,f37])).
% 0.21/0.48  fof(f241,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k10_relat_1(k1_xboole_0,X3) = X2 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = X3 | ~v1_funct_2(k1_xboole_0,X2,X3)) )),
% 0.21/0.48    inference(superposition,[],[f129,f131])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k1_relset_1(X2,X3,k1_xboole_0) = X2 | k1_xboole_0 = X3 | ~v1_funct_2(k1_xboole_0,X2,X3)) )),
% 0.21/0.48    inference(resolution,[],[f46,f37])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f239,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(k10_relat_1(X0,sK1)) | ~v1_xboole_0(X0)) ) | ~spl4_1),
% 0.21/0.48    inference(superposition,[],[f231,f38])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    ~spl4_3),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    $false | ~spl4_3),
% 0.21/0.48    inference(resolution,[],[f89,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    v1_xboole_0(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    v1_xboole_0(sK3)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f2,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK3)),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ? [X0] : v1_xboole_0(X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0)) ) | ~spl4_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f88])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    spl4_3 | spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f78,f81,f88])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ( ! [X1] : (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(X1)) )),
% 0.21/0.48    inference(resolution,[],[f39,f37])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (15048)------------------------------
% 0.21/0.48  % (15048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (15048)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (15048)Memory used [KB]: 10746
% 0.21/0.48  % (15048)Time elapsed: 0.058 s
% 0.21/0.48  % (15048)------------------------------
% 0.21/0.48  % (15048)------------------------------
% 0.21/0.48  % (15061)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (15054)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (15059)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (15046)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (15063)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.48  % (15046)Refutation not found, incomplete strategy% (15046)------------------------------
% 0.21/0.48  % (15046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (15046)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (15046)Memory used [KB]: 6140
% 0.21/0.48  % (15046)Time elapsed: 0.065 s
% 0.21/0.48  % (15046)------------------------------
% 0.21/0.48  % (15046)------------------------------
% 0.21/0.49  % (15056)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (15057)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (15047)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (15050)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (15049)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (15062)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (15051)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (15049)Refutation not found, incomplete strategy% (15049)------------------------------
% 0.21/0.50  % (15049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (15049)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (15049)Memory used [KB]: 10618
% 0.21/0.50  % (15049)Time elapsed: 0.082 s
% 0.21/0.50  % (15049)------------------------------
% 0.21/0.50  % (15049)------------------------------
% 0.21/0.50  % (15047)Refutation not found, incomplete strategy% (15047)------------------------------
% 0.21/0.50  % (15047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (15047)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (15047)Memory used [KB]: 10618
% 0.21/0.50  % (15047)Time elapsed: 0.085 s
% 0.21/0.50  % (15047)------------------------------
% 0.21/0.50  % (15047)------------------------------
% 0.21/0.50  % (15045)Success in time 0.139 s
%------------------------------------------------------------------------------
