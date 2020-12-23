%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  116 (1216 expanded)
%              Number of leaves         :   14 ( 301 expanded)
%              Depth                    :   30
%              Number of atoms          :  509 (10392 expanded)
%              Number of equality atoms :  106 (2986 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f865,plain,(
    $false ),
    inference(subsumption_resolution,[],[f864,f651])).

fof(f651,plain,(
    ~ v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f650,f345])).

fof(f345,plain,(
    ! [X0] :
      ( r2_hidden(sK2,X0)
      | ~ v2_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f336,f49])).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f336,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | ~ v2_funct_1(sK1)
      | r2_hidden(sK2,X0) ) ),
    inference(duplicate_literal_removal,[],[f324])).

fof(f324,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | ~ v2_funct_1(sK1)
      | r2_hidden(sK2,X0)
      | ~ v2_funct_1(sK1) ) ),
    inference(superposition,[],[f165,f297])).

fof(f297,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1) ),
    inference(duplicate_literal_removal,[],[f294])).

fof(f294,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f293,f93])).

fof(f93,plain,
    ( ~ sP6(sK1,sK0)
    | ~ v2_funct_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f92,f41])).

fof(f41,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ( sK2 != sK3
        & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
        & r2_hidden(sK3,sK0)
        & r2_hidden(sK2,sK0) )
      | ~ v2_funct_1(sK1) )
    & ( ! [X4,X5] :
          ( X4 = X5
          | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
          | ~ r2_hidden(X5,sK0)
          | ~ r2_hidden(X4,sK0) )
      | v2_funct_1(sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f31,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ( ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | ~ v2_funct_1(X1) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X0) )
          | v2_funct_1(X1) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ? [X3,X2] :
            ( X2 != X3
            & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
            & r2_hidden(X3,sK0)
            & r2_hidden(X2,sK0) )
        | ~ v2_funct_1(sK1) )
      & ( ! [X5,X4] :
            ( X4 = X5
            | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
            | ~ r2_hidden(X5,sK0)
            | ~ r2_hidden(X4,sK0) )
        | v2_funct_1(sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X3,X2] :
        ( X2 != X3
        & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
        & r2_hidden(X3,sK0)
        & r2_hidden(X2,sK0) )
   => ( sK2 != sK3
      & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
      & r2_hidden(sK3,sK0)
      & r2_hidden(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
            | ~ r2_hidden(X5,X0)
            | ~ r2_hidden(X4,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).

fof(f92,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ sP6(sK1,sK0) ),
    inference(subsumption_resolution,[],[f87,f42])).

fof(f42,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f87,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ sP6(sK1,sK0) ),
    inference(resolution,[],[f43,f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( k1_xboole_0 = X1
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ sP6(X3,X0) ) ),
    inference(general_splitting,[],[f67,f70_D])).

fof(f70,plain,(
    ! [X2,X0,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | ~ r2_hidden(X2,X0)
      | sP6(X3,X0) ) ),
    inference(cnf_transformation,[],[f70_D])).

fof(f70_D,plain,(
    ! [X0,X3] :
      ( ! [X2] :
          ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | ~ r2_hidden(X2,X0) )
    <=> ~ sP6(X3,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f293,plain,
    ( sP6(sK1,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(duplicate_literal_removal,[],[f292])).

fof(f292,plain,
    ( sP6(sK1,sK0)
    | ~ v2_funct_1(sK1)
    | sP6(sK1,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(resolution,[],[f212,f46])).

fof(f46,plain,
    ( r2_hidden(sK3,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f212,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | sP6(sK1,X0)
      | ~ v2_funct_1(sK1)
      | sP6(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f211,f48])).

fof(f48,plain,
    ( sK2 != sK3
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f211,plain,(
    ! [X0] :
      ( sK2 = sK3
      | ~ r2_hidden(sK3,X0)
      | sP6(sK1,X0)
      | ~ v2_funct_1(sK1)
      | sP6(sK1,sK0) ) ),
    inference(duplicate_literal_removal,[],[f203])).

fof(f203,plain,(
    ! [X0] :
      ( sK2 = sK3
      | ~ r2_hidden(sK3,X0)
      | sP6(sK1,X0)
      | ~ v2_funct_1(sK1)
      | ~ v2_funct_1(sK1)
      | sP6(sK1,sK0) ) ),
    inference(superposition,[],[f97,f82])).

fof(f82,plain,(
    ! [X2] :
      ( sK2 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,sK2))
      | ~ v2_funct_1(sK1)
      | sP6(X2,sK0) ) ),
    inference(resolution,[],[f45,f70])).

fof(f45,plain,
    ( r2_hidden(sK2,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f97,plain,(
    ! [X2] :
      ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
      | ~ r2_hidden(sK3,X2)
      | sP6(sK1,X2)
      | ~ v2_funct_1(sK1) ) ),
    inference(superposition,[],[f70,f47])).

fof(f47,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f165,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,X0)
      | ~ v2_funct_1(sK1)
      | r2_hidden(sK2,X0) ) ),
    inference(resolution,[],[f81,f64])).

% (13442)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f81,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK0,k1_zfmisc_1(X1))
      | r2_hidden(sK2,X1)
      | ~ v2_funct_1(sK1) ) ),
    inference(resolution,[],[f45,f59])).

fof(f59,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f650,plain,
    ( ~ v2_funct_1(sK1)
    | ~ r2_hidden(sK2,k1_relat_1(sK1)) ),
    inference(duplicate_literal_removal,[],[f640])).

fof(f640,plain,
    ( ~ v2_funct_1(sK1)
    | ~ r2_hidden(sK2,k1_relat_1(sK1))
    | ~ v2_funct_1(sK1) ),
    inference(resolution,[],[f347,f244])).

fof(f244,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK1))
    | ~ r2_hidden(sK2,k1_relat_1(sK1))
    | ~ v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f243,f48])).

fof(f243,plain,
    ( sK2 = sK3
    | ~ r2_hidden(sK3,k1_relat_1(sK1))
    | ~ r2_hidden(sK2,k1_relat_1(sK1))
    | ~ v2_funct_1(sK1) ),
    inference(equality_resolution,[],[f233])).

fof(f233,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
      | sK3 = X0
      | ~ r2_hidden(sK3,k1_relat_1(sK1))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v2_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f100,f94])).

fof(f94,plain,(
    v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f91,f56])).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f91,plain,
    ( v1_relat_1(sK1)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f43,f50])).

% (13444)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f100,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
      | sK3 = X0
      | ~ r2_hidden(sK3,k1_relat_1(sK1))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v2_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f99,f41])).

fof(f99,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
      | sK3 = X0
      | ~ r2_hidden(sK3,k1_relat_1(sK1))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v2_funct_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
      | sK3 = X0
      | ~ r2_hidden(sK3,k1_relat_1(sK1))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v2_funct_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ v2_funct_1(sK1) ) ),
    inference(superposition,[],[f51,f47])).

fof(f51,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK4(X0) != sK5(X0)
            & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
            & r2_hidden(sK5(X0),k1_relat_1(X0))
            & r2_hidden(sK4(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f34,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK4(X0) != sK5(X0)
        & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
        & r2_hidden(sK5(X0),k1_relat_1(X0))
        & r2_hidden(sK4(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f347,plain,(
    ! [X0] :
      ( r2_hidden(sK3,X0)
      | ~ v2_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f334,f49])).

fof(f334,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | ~ v2_funct_1(sK1)
      | r2_hidden(sK3,X0) ) ),
    inference(duplicate_literal_removal,[],[f326])).

fof(f326,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | ~ v2_funct_1(sK1)
      | r2_hidden(sK3,X0)
      | ~ v2_funct_1(sK1) ) ),
    inference(superposition,[],[f171,f297])).

fof(f171,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,X0)
      | ~ v2_funct_1(sK1)
      | r2_hidden(sK3,X0) ) ),
    inference(resolution,[],[f84,f64])).

fof(f84,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK0,k1_zfmisc_1(X1))
      | r2_hidden(sK3,X1)
      | ~ v2_funct_1(sK1) ) ),
    inference(resolution,[],[f46,f59])).

fof(f864,plain,(
    v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f281,f685])).

fof(f685,plain,(
    ~ r2_hidden(sK4(sK1),sK0) ),
    inference(subsumption_resolution,[],[f684,f94])).

fof(f684,plain,
    ( ~ r2_hidden(sK4(sK1),sK0)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f683,f41])).

fof(f683,plain,
    ( ~ r2_hidden(sK4(sK1),sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f682,f651])).

fof(f682,plain,
    ( ~ r2_hidden(sK4(sK1),sK0)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f679,f134])).

fof(f134,plain,(
    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f126,f64])).

fof(f126,plain,(
    r1_tarski(k1_relat_1(sK1),sK0) ),
    inference(subsumption_resolution,[],[f125,f94])).

fof(f125,plain,
    ( r1_tarski(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f86,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f86,plain,(
    v4_relat_1(sK1,sK0) ),
    inference(resolution,[],[f43,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f679,plain,
    ( ~ r2_hidden(sK4(sK1),sK0)
    | ~ m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f677,f53])).

fof(f53,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK5(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f677,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(sK1),X0)
      | ~ r2_hidden(sK4(sK1),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f277,f651])).

fof(f277,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK1),sK0)
      | v2_funct_1(sK1)
      | ~ r2_hidden(sK5(sK1),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f255,f59])).

fof(f255,plain,
    ( ~ r2_hidden(sK5(sK1),sK0)
    | ~ r2_hidden(sK4(sK1),sK0)
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f254,f154])).

fof(f154,plain,
    ( sK4(sK1) != sK5(sK1)
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f76,f94])).

fof(f76,plain,
    ( v2_funct_1(sK1)
    | sK4(sK1) != sK5(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f41,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK4(X0) != sK5(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f254,plain,
    ( sK4(sK1) = sK5(sK1)
    | ~ r2_hidden(sK4(sK1),sK0)
    | ~ r2_hidden(sK5(sK1),sK0)
    | v2_funct_1(sK1) ),
    inference(equality_resolution,[],[f245])).

fof(f245,plain,(
    ! [X1] :
      ( k1_funct_1(sK1,X1) != k1_funct_1(sK1,sK4(sK1))
      | sK5(sK1) = X1
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(sK5(sK1),sK0)
      | v2_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f110,f94])).

fof(f110,plain,(
    ! [X1] :
      ( k1_funct_1(sK1,X1) != k1_funct_1(sK1,sK4(sK1))
      | sK5(sK1) = X1
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(sK5(sK1),sK0)
      | v2_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f109,f41])).

fof(f109,plain,(
    ! [X1] :
      ( k1_funct_1(sK1,X1) != k1_funct_1(sK1,sK4(sK1))
      | sK5(sK1) = X1
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(sK5(sK1),sK0)
      | v2_funct_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,(
    ! [X1] :
      ( k1_funct_1(sK1,X1) != k1_funct_1(sK1,sK4(sK1))
      | sK5(sK1) = X1
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(sK5(sK1),sK0)
      | v2_funct_1(sK1)
      | v2_funct_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f44,f54])).

fof(f54,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f44,plain,(
    ! [X4,X5] :
      ( k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
      | X4 = X5
      | ~ r2_hidden(X5,sK0)
      | ~ r2_hidden(X4,sK0)
      | v2_funct_1(sK1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f281,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f142,f134])).

fof(f142,plain,(
    ! [X3] :
      ( ~ m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X3))
      | r2_hidden(sK4(sK1),X3)
      | v2_funct_1(sK1) ) ),
    inference(resolution,[],[f138,f59])).

fof(f138,plain,
    ( r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f73,f94])).

fof(f73,plain,
    ( v2_funct_1(sK1)
    | r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f41,f52])).

fof(f52,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK4(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:30:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (13449)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.49  % (13439)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.49  % (13433)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.49  % (13433)Refutation not found, incomplete strategy% (13433)------------------------------
% 0.21/0.49  % (13433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13433)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (13433)Memory used [KB]: 10618
% 0.21/0.49  % (13433)Time elapsed: 0.086 s
% 0.21/0.49  % (13433)------------------------------
% 0.21/0.49  % (13433)------------------------------
% 0.21/0.49  % (13427)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (13445)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.50  % (13427)Refutation not found, incomplete strategy% (13427)------------------------------
% 0.21/0.50  % (13427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (13427)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (13427)Memory used [KB]: 10618
% 0.21/0.50  % (13427)Time elapsed: 0.083 s
% 0.21/0.50  % (13427)------------------------------
% 0.21/0.50  % (13427)------------------------------
% 0.21/0.50  % (13447)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.50  % (13429)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (13431)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (13448)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (13441)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (13435)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (13438)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (13437)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (13432)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (13428)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (13430)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (13428)Refutation not found, incomplete strategy% (13428)------------------------------
% 0.21/0.52  % (13428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13428)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13428)Memory used [KB]: 10618
% 0.21/0.52  % (13428)Time elapsed: 0.100 s
% 0.21/0.52  % (13428)------------------------------
% 0.21/0.52  % (13428)------------------------------
% 0.21/0.52  % (13451)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (13443)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (13445)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f865,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f864,f651])).
% 0.21/0.53  fof(f651,plain,(
% 0.21/0.53    ~v2_funct_1(sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f650,f345])).
% 0.21/0.53  fof(f345,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK2,X0) | ~v2_funct_1(sK1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f336,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.53  fof(f336,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~v2_funct_1(sK1) | r2_hidden(sK2,X0)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f324])).
% 0.21/0.53  fof(f324,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~v2_funct_1(sK1) | r2_hidden(sK2,X0) | ~v2_funct_1(sK1)) )),
% 0.21/0.53    inference(superposition,[],[f165,f297])).
% 0.21/0.53  fof(f297,plain,(
% 0.21/0.53    k1_xboole_0 = sK0 | ~v2_funct_1(sK1)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f294])).
% 0.21/0.53  fof(f294,plain,(
% 0.21/0.53    ~v2_funct_1(sK1) | ~v2_funct_1(sK1) | k1_xboole_0 = sK0),
% 0.21/0.53    inference(resolution,[],[f293,f93])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ~sP6(sK1,sK0) | ~v2_funct_1(sK1) | k1_xboole_0 = sK0),
% 0.21/0.53    inference(subsumption_resolution,[],[f92,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    v1_funct_1(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ((sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0)) | ~v2_funct_1(sK1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0)) | v2_funct_1(sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f31,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) | ~v2_funct_1(sK1)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0)) | v2_funct_1(sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) => (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.53    inference(rectify,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.53    inference(flattening,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.53    inference(flattening,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.21/0.53    inference(negated_conjecture,[],[f12])).
% 0.21/0.53  fof(f12,conjecture,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    k1_xboole_0 = sK0 | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~sP6(sK1,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f87,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    k1_xboole_0 = sK0 | ~v2_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~sP6(sK1,sK0)),
% 0.21/0.53    inference(resolution,[],[f43,f71])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (k1_xboole_0 = X1 | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~sP6(X3,X0)) )),
% 0.21/0.53    inference(general_splitting,[],[f67,f70_D])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X2,X0,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | ~r2_hidden(X2,X0) | sP6(X3,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f70_D])).
% 0.21/0.53  fof(f70_D,plain,(
% 0.21/0.53    ( ! [X0,X3] : (( ! [X2] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | ~r2_hidden(X2,X0)) ) <=> ~sP6(X3,X0)) )),
% 0.21/0.53    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.53    inference(flattening,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f293,plain,(
% 0.21/0.53    sP6(sK1,sK0) | ~v2_funct_1(sK1)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f292])).
% 0.21/0.53  fof(f292,plain,(
% 0.21/0.53    sP6(sK1,sK0) | ~v2_funct_1(sK1) | sP6(sK1,sK0) | ~v2_funct_1(sK1)),
% 0.21/0.53    inference(resolution,[],[f212,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    r2_hidden(sK3,sK0) | ~v2_funct_1(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f212,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK3,X0) | sP6(sK1,X0) | ~v2_funct_1(sK1) | sP6(sK1,sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f211,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    sK2 != sK3 | ~v2_funct_1(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f211,plain,(
% 0.21/0.53    ( ! [X0] : (sK2 = sK3 | ~r2_hidden(sK3,X0) | sP6(sK1,X0) | ~v2_funct_1(sK1) | sP6(sK1,sK0)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f203])).
% 0.21/0.53  fof(f203,plain,(
% 0.21/0.53    ( ! [X0] : (sK2 = sK3 | ~r2_hidden(sK3,X0) | sP6(sK1,X0) | ~v2_funct_1(sK1) | ~v2_funct_1(sK1) | sP6(sK1,sK0)) )),
% 0.21/0.53    inference(superposition,[],[f97,f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X2] : (sK2 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,sK2)) | ~v2_funct_1(sK1) | sP6(X2,sK0)) )),
% 0.21/0.53    inference(resolution,[],[f45,f70])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    r2_hidden(sK2,sK0) | ~v2_funct_1(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ( ! [X2] : (sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~r2_hidden(sK3,X2) | sP6(sK1,X2) | ~v2_funct_1(sK1)) )),
% 0.21/0.53    inference(superposition,[],[f70,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~v2_funct_1(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(sK0,X0) | ~v2_funct_1(sK1) | r2_hidden(sK2,X0)) )),
% 0.21/0.53    inference(resolution,[],[f81,f64])).
% 0.21/0.53  % (13442)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.53    inference(nnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ( ! [X1] : (~m1_subset_1(sK0,k1_zfmisc_1(X1)) | r2_hidden(sK2,X1) | ~v2_funct_1(sK1)) )),
% 0.21/0.53    inference(resolution,[],[f45,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.53  fof(f650,plain,(
% 0.21/0.53    ~v2_funct_1(sK1) | ~r2_hidden(sK2,k1_relat_1(sK1))),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f640])).
% 0.21/0.53  fof(f640,plain,(
% 0.21/0.53    ~v2_funct_1(sK1) | ~r2_hidden(sK2,k1_relat_1(sK1)) | ~v2_funct_1(sK1)),
% 0.21/0.53    inference(resolution,[],[f347,f244])).
% 0.21/0.53  fof(f244,plain,(
% 0.21/0.53    ~r2_hidden(sK3,k1_relat_1(sK1)) | ~r2_hidden(sK2,k1_relat_1(sK1)) | ~v2_funct_1(sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f243,f48])).
% 0.21/0.53  fof(f243,plain,(
% 0.21/0.53    sK2 = sK3 | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~r2_hidden(sK2,k1_relat_1(sK1)) | ~v2_funct_1(sK1)),
% 0.21/0.53    inference(equality_resolution,[],[f233])).
% 0.21/0.53  fof(f233,plain,(
% 0.21/0.53    ( ! [X0] : (k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | sK3 = X0 | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v2_funct_1(sK1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f100,f94])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    v1_relat_1(sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f91,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    v1_relat_1(sK1) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 0.21/0.53    inference(resolution,[],[f43,f50])).
% 0.21/0.53  % (13444)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    ( ! [X0] : (k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | sK3 = X0 | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f99,f41])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    ( ! [X0] : (k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | sK3 = X0 | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f95])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    ( ! [X0] : (k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | sK3 = X0 | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v2_funct_1(sK1)) )),
% 0.21/0.53    inference(superposition,[],[f51,f47])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X4,X0,X3] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0] : (((v2_funct_1(X0) | (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f34,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(rectify,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 0.21/0.53  fof(f347,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK3,X0) | ~v2_funct_1(sK1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f334,f49])).
% 0.21/0.53  fof(f334,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~v2_funct_1(sK1) | r2_hidden(sK3,X0)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f326])).
% 0.21/0.53  fof(f326,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~v2_funct_1(sK1) | r2_hidden(sK3,X0) | ~v2_funct_1(sK1)) )),
% 0.21/0.53    inference(superposition,[],[f171,f297])).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(sK0,X0) | ~v2_funct_1(sK1) | r2_hidden(sK3,X0)) )),
% 0.21/0.53    inference(resolution,[],[f84,f64])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X1] : (~m1_subset_1(sK0,k1_zfmisc_1(X1)) | r2_hidden(sK3,X1) | ~v2_funct_1(sK1)) )),
% 0.21/0.53    inference(resolution,[],[f46,f59])).
% 0.21/0.53  fof(f864,plain,(
% 0.21/0.53    v2_funct_1(sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f281,f685])).
% 0.21/0.53  fof(f685,plain,(
% 0.21/0.53    ~r2_hidden(sK4(sK1),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f684,f94])).
% 0.21/0.53  fof(f684,plain,(
% 0.21/0.53    ~r2_hidden(sK4(sK1),sK0) | ~v1_relat_1(sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f683,f41])).
% 0.21/0.53  fof(f683,plain,(
% 0.21/0.53    ~r2_hidden(sK4(sK1),sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f682,f651])).
% 0.21/0.53  fof(f682,plain,(
% 0.21/0.53    ~r2_hidden(sK4(sK1),sK0) | v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f679,f134])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))),
% 0.21/0.53    inference(resolution,[],[f126,f64])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    r1_tarski(k1_relat_1(sK1),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f125,f94])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    r1_tarski(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1)),
% 0.21/0.53    inference(resolution,[],[f86,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    v4_relat_1(sK1,sK0)),
% 0.21/0.53    inference(resolution,[],[f43,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.53    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.53  fof(f679,plain,(
% 0.21/0.53    ~r2_hidden(sK4(sK1),sK0) | ~m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) | v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.53    inference(resolution,[],[f677,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK5(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f677,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK5(sK1),X0) | ~r2_hidden(sK4(sK1),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f277,f651])).
% 0.21/0.53  fof(f277,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK4(sK1),sK0) | v2_funct_1(sK1) | ~r2_hidden(sK5(sK1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 0.21/0.53    inference(resolution,[],[f255,f59])).
% 0.21/0.53  fof(f255,plain,(
% 0.21/0.53    ~r2_hidden(sK5(sK1),sK0) | ~r2_hidden(sK4(sK1),sK0) | v2_funct_1(sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f254,f154])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    sK4(sK1) != sK5(sK1) | v2_funct_1(sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f76,f94])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    v2_funct_1(sK1) | sK4(sK1) != sK5(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.53    inference(resolution,[],[f41,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0] : (v2_funct_1(X0) | sK4(X0) != sK5(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f254,plain,(
% 0.21/0.53    sK4(sK1) = sK5(sK1) | ~r2_hidden(sK4(sK1),sK0) | ~r2_hidden(sK5(sK1),sK0) | v2_funct_1(sK1)),
% 0.21/0.53    inference(equality_resolution,[],[f245])).
% 0.21/0.53  fof(f245,plain,(
% 0.21/0.53    ( ! [X1] : (k1_funct_1(sK1,X1) != k1_funct_1(sK1,sK4(sK1)) | sK5(sK1) = X1 | ~r2_hidden(X1,sK0) | ~r2_hidden(sK5(sK1),sK0) | v2_funct_1(sK1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f110,f94])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    ( ! [X1] : (k1_funct_1(sK1,X1) != k1_funct_1(sK1,sK4(sK1)) | sK5(sK1) = X1 | ~r2_hidden(X1,sK0) | ~r2_hidden(sK5(sK1),sK0) | v2_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f109,f41])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    ( ! [X1] : (k1_funct_1(sK1,X1) != k1_funct_1(sK1,sK4(sK1)) | sK5(sK1) = X1 | ~r2_hidden(X1,sK0) | ~r2_hidden(sK5(sK1),sK0) | v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f103])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    ( ! [X1] : (k1_funct_1(sK1,X1) != k1_funct_1(sK1,sK4(sK1)) | sK5(sK1) = X1 | ~r2_hidden(X1,sK0) | ~r2_hidden(sK5(sK1),sK0) | v2_funct_1(sK1) | v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.21/0.53    inference(superposition,[],[f44,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X4,X5] : (k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | X4 = X5 | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0) | v2_funct_1(sK1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f281,plain,(
% 0.21/0.53    r2_hidden(sK4(sK1),sK0) | v2_funct_1(sK1)),
% 0.21/0.53    inference(resolution,[],[f142,f134])).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    ( ! [X3] : (~m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X3)) | r2_hidden(sK4(sK1),X3) | v2_funct_1(sK1)) )),
% 0.21/0.53    inference(resolution,[],[f138,f59])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    r2_hidden(sK4(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f73,f94])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    v2_funct_1(sK1) | r2_hidden(sK4(sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.21/0.53    inference(resolution,[],[f41,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK4(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (13445)------------------------------
% 0.21/0.53  % (13445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13445)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (13445)Memory used [KB]: 1918
% 0.21/0.53  % (13445)Time elapsed: 0.126 s
% 0.21/0.53  % (13445)------------------------------
% 0.21/0.53  % (13445)------------------------------
% 0.21/0.53  % (13440)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (13450)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (13446)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.54  % (13452)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.54  % (13426)Success in time 0.18 s
%------------------------------------------------------------------------------
