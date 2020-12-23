%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:21 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  159 (40450 expanded)
%              Number of leaves         :   17 (9350 expanded)
%              Depth                    :   36
%              Number of atoms          :  434 (183465 expanded)
%              Number of equality atoms :  148 (23565 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f644,plain,(
    $false ),
    inference(subsumption_resolution,[],[f635,f636])).

fof(f636,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f562,f613])).

fof(f613,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f51,f611])).

fof(f611,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f607,f50])).

fof(f50,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
      | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
      | ~ v1_funct_1(sK2) )
    & r1_tarski(k2_relat_1(sK2),sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f41])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
        | ~ v1_funct_1(sK2) )
      & r1_tarski(k2_relat_1(sK2),sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f607,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f599])).

fof(f599,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f57,f504])).

fof(f504,plain,(
    k1_xboole_0 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f503,f382])).

fof(f382,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f352,f376])).

fof(f376,plain,(
    k1_xboole_0 = k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f373,f65])).

fof(f65,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f373,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)
    | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)) ),
    inference(trivial_inequality_removal,[],[f365])).

fof(f365,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)
    | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)) ),
    inference(superposition,[],[f57,f352])).

fof(f352,plain,(
    k1_xboole_0 = k2_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)) ),
    inference(global_subsumption,[],[f338,f350])).

fof(f350,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)) ),
    inference(resolution,[],[f345,f99])).

fof(f99,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k2_relat_1(k2_zfmisc_1(X3,X2)))
      | k2_relat_1(k2_zfmisc_1(X3,X2)) = X2 ) ),
    inference(resolution,[],[f71,f66])).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
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

fof(f345,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(resolution,[],[f310,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f310,plain,(
    r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))) ),
    inference(backward_demodulation,[],[f285,f304])).

fof(f304,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f302,f52])).

fof(f52,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f302,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f299,f141])).

fof(f141,plain,(
    ! [X2] :
      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X2)))
      | ~ r1_tarski(k2_relat_1(sK2),X2) ) ),
    inference(resolution,[],[f138,f87])).

fof(f87,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(sK2),X1)
      | ~ r1_tarski(k2_relat_1(sK2),X0)
      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(resolution,[],[f74,f50])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f299,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f298,f94])).

fof(f94,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    inference(subsumption_resolution,[],[f53,f51])).

fof(f53,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f298,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f297,f52])).

fof(f297,plain,
    ( k1_xboole_0 = sK1
    | v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f271,f145])).

fof(f145,plain,(
    ! [X1] :
      ( sP0(k1_relat_1(sK2),sK2,X1)
      | ~ r1_tarski(k2_relat_1(sK2),X1) ) ),
    inference(resolution,[],[f141,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f35,f39])).

fof(f39,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f271,plain,
    ( ~ sP0(k1_relat_1(sK2),sK2,sK1)
    | k1_xboole_0 = sK1
    | v1_funct_2(sK2,k1_relat_1(sK2),sK1) ),
    inference(trivial_inequality_removal,[],[f269])).

fof(f269,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | k1_xboole_0 = sK1
    | ~ sP0(k1_relat_1(sK2),sK2,sK1) ),
    inference(superposition,[],[f78,f150])).

fof(f150,plain,(
    k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),sK1,sK2) ),
    inference(resolution,[],[f144,f52])).

fof(f144,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK2),X0)
      | k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),X0,sK2) ) ),
    inference(resolution,[],[f141,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) != X0
      | v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f285,plain,(
    r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),sK1),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))) ),
    inference(subsumption_resolution,[],[f277,f65])).

fof(f277,plain,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),sK1),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)) ),
    inference(superposition,[],[f55,f263])).

fof(f263,plain,(
    k1_relat_1(sK2) = k1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)) ),
    inference(resolution,[],[f228,f52])).

fof(f228,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK2),X0)
      | k1_relat_1(sK2) = k1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),X0)) ) ),
    inference(resolution,[],[f225,f146])).

fof(f146,plain,(
    ! [X2] :
      ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),X2))
      | ~ r1_tarski(k2_relat_1(sK2),X2) ) ),
    inference(resolution,[],[f141,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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

fof(f225,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),X0))
      | k1_relat_1(sK2) = k1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),X0)) ) ),
    inference(resolution,[],[f122,f50])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),X1))
      | k1_relat_1(X0) = k1_relat_1(k2_zfmisc_1(k1_relat_1(X0),X1)) ) ),
    inference(subsumption_resolution,[],[f121,f65])).

fof(f121,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k2_zfmisc_1(k1_relat_1(X0),X1))
      | ~ r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),X1))
      | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(X0),X1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f100,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f100,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X4,k1_relat_1(k2_zfmisc_1(X4,X5)))
      | k1_relat_1(k2_zfmisc_1(X4,X5)) = X4 ) ),
    inference(resolution,[],[f71,f67])).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).

fof(f55,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f338,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f330,f65])).

fof(f330,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))
    | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)) ),
    inference(superposition,[],[f58,f309])).

fof(f309,plain,(
    k1_relat_1(sK2) = k1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)) ),
    inference(backward_demodulation,[],[f263,f304])).

fof(f58,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f503,plain,(
    k2_relat_1(sK2) = k2_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f467,f497])).

fof(f497,plain,(
    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2)) ),
    inference(global_subsumption,[],[f415,f447])).

fof(f447,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f446,f427])).

fof(f427,plain,(
    k1_xboole_0 = k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f376,f378])).

fof(f378,plain,(
    k1_relat_1(sK2) = k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f309,f376])).

fof(f446,plain,(
    k1_xboole_0 = k1_relat_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f445,f378])).

fof(f445,plain,(
    k1_xboole_0 = k1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f372,f65])).

fof(f372,plain,
    ( k1_xboole_0 = k1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))
    | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)) ),
    inference(trivial_inequality_removal,[],[f366])).

fof(f366,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))
    | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)) ),
    inference(superposition,[],[f59,f352])).

fof(f59,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f415,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f251,f378])).

fof(f251,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2)) ),
    inference(inner_rewriting,[],[f250])).

fof(f250,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f241,f65])).

fof(f241,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(superposition,[],[f56,f227])).

fof(f227,plain,(
    k1_relat_1(sK2) = k1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(resolution,[],[f225,f116])).

fof(f116,plain,(
    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(resolution,[],[f114,f72])).

fof(f114,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    inference(subsumption_resolution,[],[f113,f50])).

fof(f113,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f64,f51])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f467,plain,(
    k2_relat_1(sK2) = k2_relat_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2))) ),
    inference(backward_demodulation,[],[f400,f447])).

fof(f400,plain,(
    k2_relat_1(sK2) = k2_relat_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(sK2))) ),
    inference(backward_demodulation,[],[f162,f378])).

fof(f162,plain,(
    k2_relat_1(sK2) = k2_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(resolution,[],[f160,f116])).

fof(f160,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,k2_zfmisc_1(X0,k2_relat_1(sK2)))
      | k2_relat_1(sK2) = k2_relat_1(k2_zfmisc_1(X0,k2_relat_1(sK2))) ) ),
    inference(resolution,[],[f120,f50])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))
      | k2_relat_1(X1) = k2_relat_1(k2_zfmisc_1(X0,k2_relat_1(X1))) ) ),
    inference(subsumption_resolution,[],[f119,f65])).

fof(f119,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k2_relat_1(k2_zfmisc_1(X0,k2_relat_1(X1)))
      | ~ r1_tarski(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))
      | ~ v1_relat_1(k2_zfmisc_1(X0,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f99,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f562,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f561,f449])).

fof(f449,plain,(
    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f423,f447])).

fof(f423,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f311,f378])).

fof(f311,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f287,f304])).

fof(f287,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(inner_rewriting,[],[f286])).

fof(f286,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = k2_zfmisc_1(k1_relat_1(sK2),sK1) ),
    inference(subsumption_resolution,[],[f278,f65])).

fof(f278,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = k2_zfmisc_1(k1_relat_1(sK2),sK1)
    | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)) ),
    inference(superposition,[],[f56,f263])).

fof(f561,plain,
    ( v1_funct_2(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f560,f447])).

fof(f560,plain,
    ( v1_funct_2(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0),k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f559,f504])).

fof(f559,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | v1_funct_2(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(sK2)),k1_relat_1(k1_xboole_0),k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f558,f449])).

fof(f558,plain,
    ( ~ v1_funct_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | v1_funct_2(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(sK2)),k1_relat_1(k1_xboole_0),k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f488,f504])).

fof(f488,plain,
    ( ~ v1_funct_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2)))
    | v1_funct_2(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(sK2)),k1_relat_1(k1_xboole_0),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f435,f447])).

fof(f435,plain,
    ( v1_funct_2(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(sK2)),k1_relat_1(k1_xboole_0),k2_relat_1(sK2))
    | ~ v1_funct_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(sK2))) ),
    inference(forward_demodulation,[],[f413,f378])).

fof(f413,plain,
    ( ~ v1_funct_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(sK2)))
    | v1_funct_2(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f231,f378])).

fof(f231,plain,
    ( v1_funct_2(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(backward_demodulation,[],[f182,f227])).

fof(f182,plain,
    ( v1_funct_2(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_relat_1(sK2))
    | ~ v1_funct_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(subsumption_resolution,[],[f172,f65])).

fof(f172,plain,
    ( v1_funct_2(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_relat_1(sK2))
    | ~ v1_funct_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(superposition,[],[f63,f162])).

fof(f63,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f635,plain,(
    ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f570,f611])).

fof(f570,plain,(
    ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f494,f501])).

fof(f501,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f455,f497])).

fof(f455,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f385,f447])).

fof(f385,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f114,f378])).

fof(f494,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f441,f447])).

fof(f441,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f381,f378])).

fof(f381,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) ),
    inference(backward_demodulation,[],[f318,f376])).

fof(f318,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) ),
    inference(forward_demodulation,[],[f306,f304])).

fof(f306,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1) ),
    inference(backward_demodulation,[],[f94,f304])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:10:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (24528)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.47  % (24535)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.49  % (24526)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (24518)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (24538)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (24530)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (24521)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (24522)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (24520)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (24524)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (24519)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (24537)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (24527)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (24525)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (24540)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (24534)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (24541)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (24532)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (24517)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (24517)Refutation not found, incomplete strategy% (24517)------------------------------
% 0.21/0.52  % (24517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (24517)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (24517)Memory used [KB]: 10618
% 0.21/0.52  % (24517)Time elapsed: 0.116 s
% 0.21/0.52  % (24517)------------------------------
% 0.21/0.52  % (24517)------------------------------
% 0.21/0.52  % (24529)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (24531)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.53  % (24516)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.53  % (24539)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.54  % (24533)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.54  % (24536)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.41/0.54  % (24523)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.57/0.56  % (24521)Refutation not found, incomplete strategy% (24521)------------------------------
% 1.57/0.56  % (24521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (24521)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.56  
% 1.57/0.56  % (24521)Memory used [KB]: 6524
% 1.57/0.56  % (24521)Time elapsed: 0.143 s
% 1.57/0.56  % (24521)------------------------------
% 1.57/0.56  % (24521)------------------------------
% 1.57/0.56  % (24519)Refutation found. Thanks to Tanya!
% 1.57/0.56  % SZS status Theorem for theBenchmark
% 1.57/0.56  % SZS output start Proof for theBenchmark
% 1.57/0.56  fof(f644,plain,(
% 1.57/0.56    $false),
% 1.57/0.56    inference(subsumption_resolution,[],[f635,f636])).
% 1.57/0.56  fof(f636,plain,(
% 1.57/0.56    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.57/0.56    inference(subsumption_resolution,[],[f562,f613])).
% 1.57/0.56  fof(f613,plain,(
% 1.57/0.56    v1_funct_1(k1_xboole_0)),
% 1.57/0.56    inference(backward_demodulation,[],[f51,f611])).
% 1.57/0.56  fof(f611,plain,(
% 1.57/0.56    k1_xboole_0 = sK2),
% 1.57/0.56    inference(subsumption_resolution,[],[f607,f50])).
% 1.57/0.56  fof(f50,plain,(
% 1.57/0.56    v1_relat_1(sK2)),
% 1.57/0.56    inference(cnf_transformation,[],[f42])).
% 1.57/0.56  fof(f42,plain,(
% 1.57/0.56    (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_funct_1(sK2)) & r1_tarski(k2_relat_1(sK2),sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.57/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f41])).
% 1.57/0.56  fof(f41,plain,(
% 1.57/0.56    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_funct_1(sK2)) & r1_tarski(k2_relat_1(sK2),sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.57/0.56    introduced(choice_axiom,[])).
% 1.57/0.56  fof(f21,plain,(
% 1.57/0.56    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.57/0.56    inference(flattening,[],[f20])).
% 1.57/0.56  fof(f20,plain,(
% 1.57/0.56    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.57/0.56    inference(ennf_transformation,[],[f19])).
% 1.57/0.56  fof(f19,negated_conjecture,(
% 1.57/0.56    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.57/0.56    inference(negated_conjecture,[],[f18])).
% 1.57/0.56  fof(f18,conjecture,(
% 1.57/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 1.57/0.56  fof(f607,plain,(
% 1.57/0.56    k1_xboole_0 = sK2 | ~v1_relat_1(sK2)),
% 1.57/0.56    inference(trivial_inequality_removal,[],[f599])).
% 1.57/0.56  fof(f599,plain,(
% 1.57/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | ~v1_relat_1(sK2)),
% 1.57/0.56    inference(superposition,[],[f57,f504])).
% 1.57/0.56  fof(f504,plain,(
% 1.57/0.56    k1_xboole_0 = k2_relat_1(sK2)),
% 1.57/0.56    inference(forward_demodulation,[],[f503,f382])).
% 1.57/0.56  fof(f382,plain,(
% 1.57/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.57/0.56    inference(backward_demodulation,[],[f352,f376])).
% 1.57/0.56  fof(f376,plain,(
% 1.57/0.56    k1_xboole_0 = k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)),
% 1.57/0.56    inference(subsumption_resolution,[],[f373,f65])).
% 1.57/0.56  fof(f65,plain,(
% 1.57/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.57/0.56    inference(cnf_transformation,[],[f5])).
% 1.57/0.56  fof(f5,axiom,(
% 1.57/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.57/0.56  fof(f373,plain,(
% 1.57/0.56    k1_xboole_0 = k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0) | ~v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))),
% 1.57/0.56    inference(trivial_inequality_removal,[],[f365])).
% 1.57/0.56  fof(f365,plain,(
% 1.57/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0) | ~v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))),
% 1.57/0.56    inference(superposition,[],[f57,f352])).
% 1.57/0.56  fof(f352,plain,(
% 1.57/0.56    k1_xboole_0 = k2_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))),
% 1.57/0.56    inference(global_subsumption,[],[f338,f350])).
% 1.57/0.56  fof(f350,plain,(
% 1.57/0.56    k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = k2_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))),
% 1.57/0.56    inference(resolution,[],[f345,f99])).
% 1.57/0.56  fof(f99,plain,(
% 1.57/0.56    ( ! [X2,X3] : (~r1_tarski(X2,k2_relat_1(k2_zfmisc_1(X3,X2))) | k2_relat_1(k2_zfmisc_1(X3,X2)) = X2) )),
% 1.57/0.56    inference(resolution,[],[f71,f66])).
% 1.57/0.56  fof(f66,plain,(
% 1.57/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f7])).
% 1.57/0.56  fof(f7,axiom,(
% 1.57/0.56    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).
% 1.57/0.56  fof(f71,plain,(
% 1.57/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.57/0.56    inference(cnf_transformation,[],[f45])).
% 1.57/0.56  fof(f45,plain,(
% 1.57/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.57/0.56    inference(flattening,[],[f44])).
% 1.57/0.56  fof(f44,plain,(
% 1.57/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.57/0.56    inference(nnf_transformation,[],[f2])).
% 1.57/0.56  fof(f2,axiom,(
% 1.57/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.57/0.56  fof(f345,plain,(
% 1.57/0.56    r1_tarski(k1_xboole_0,k2_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) | k1_xboole_0 = k1_relat_1(sK2)),
% 1.57/0.56    inference(resolution,[],[f310,f86])).
% 1.57/0.56  fof(f86,plain,(
% 1.57/0.56    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 1.57/0.56    inference(cnf_transformation,[],[f38])).
% 1.57/0.56  fof(f38,plain,(
% 1.57/0.56    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 1.57/0.56    inference(ennf_transformation,[],[f3])).
% 1.57/0.56  fof(f3,axiom,(
% 1.57/0.56    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 1.57/0.56  fof(f310,plain,(
% 1.57/0.56    r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))))),
% 1.57/0.56    inference(backward_demodulation,[],[f285,f304])).
% 1.57/0.56  fof(f304,plain,(
% 1.57/0.56    k1_xboole_0 = sK1),
% 1.57/0.56    inference(subsumption_resolution,[],[f302,f52])).
% 1.57/0.56  fof(f52,plain,(
% 1.57/0.56    r1_tarski(k2_relat_1(sK2),sK1)),
% 1.57/0.56    inference(cnf_transformation,[],[f42])).
% 1.57/0.56  fof(f302,plain,(
% 1.57/0.56    k1_xboole_0 = sK1 | ~r1_tarski(k2_relat_1(sK2),sK1)),
% 1.57/0.56    inference(resolution,[],[f299,f141])).
% 1.57/0.56  fof(f141,plain,(
% 1.57/0.56    ( ! [X2] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X2))) | ~r1_tarski(k2_relat_1(sK2),X2)) )),
% 1.57/0.56    inference(resolution,[],[f138,f87])).
% 1.57/0.56  fof(f87,plain,(
% 1.57/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.57/0.56    inference(equality_resolution,[],[f70])).
% 1.57/0.56  fof(f70,plain,(
% 1.57/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.57/0.56    inference(cnf_transformation,[],[f45])).
% 1.57/0.56  fof(f138,plain,(
% 1.57/0.56    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK2),X1) | ~r1_tarski(k2_relat_1(sK2),X0) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 1.57/0.56    inference(resolution,[],[f74,f50])).
% 1.57/0.56  fof(f74,plain,(
% 1.57/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.56    inference(cnf_transformation,[],[f32])).
% 1.57/0.56  fof(f32,plain,(
% 1.57/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.57/0.56    inference(flattening,[],[f31])).
% 1.57/0.56  fof(f31,plain,(
% 1.57/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.57/0.56    inference(ennf_transformation,[],[f13])).
% 1.57/0.56  fof(f13,axiom,(
% 1.57/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.57/0.56  fof(f299,plain,(
% 1.57/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | k1_xboole_0 = sK1),
% 1.57/0.56    inference(resolution,[],[f298,f94])).
% 1.57/0.56  fof(f94,plain,(
% 1.57/0.56    ~v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 1.57/0.56    inference(subsumption_resolution,[],[f53,f51])).
% 1.57/0.56  fof(f53,plain,(
% 1.57/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_funct_1(sK2)),
% 1.57/0.56    inference(cnf_transformation,[],[f42])).
% 1.57/0.56  fof(f298,plain,(
% 1.57/0.56    v1_funct_2(sK2,k1_relat_1(sK2),sK1) | k1_xboole_0 = sK1),
% 1.57/0.56    inference(subsumption_resolution,[],[f297,f52])).
% 1.57/0.56  fof(f297,plain,(
% 1.57/0.56    k1_xboole_0 = sK1 | v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~r1_tarski(k2_relat_1(sK2),sK1)),
% 1.57/0.56    inference(resolution,[],[f271,f145])).
% 1.57/0.56  fof(f145,plain,(
% 1.57/0.56    ( ! [X1] : (sP0(k1_relat_1(sK2),sK2,X1) | ~r1_tarski(k2_relat_1(sK2),X1)) )),
% 1.57/0.56    inference(resolution,[],[f141,f80])).
% 1.57/0.56  fof(f80,plain,(
% 1.57/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f49])).
% 1.57/0.56  fof(f49,plain,(
% 1.57/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.56    inference(nnf_transformation,[],[f40])).
% 1.57/0.56  fof(f40,plain,(
% 1.57/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.56    inference(definition_folding,[],[f35,f39])).
% 1.57/0.56  fof(f39,plain,(
% 1.57/0.56    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.57/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.57/0.56  fof(f35,plain,(
% 1.57/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.56    inference(flattening,[],[f34])).
% 1.57/0.56  fof(f34,plain,(
% 1.57/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.56    inference(ennf_transformation,[],[f16])).
% 1.57/0.56  fof(f16,axiom,(
% 1.57/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.57/0.56  fof(f271,plain,(
% 1.57/0.56    ~sP0(k1_relat_1(sK2),sK2,sK1) | k1_xboole_0 = sK1 | v1_funct_2(sK2,k1_relat_1(sK2),sK1)),
% 1.57/0.56    inference(trivial_inequality_removal,[],[f269])).
% 1.57/0.56  fof(f269,plain,(
% 1.57/0.56    k1_relat_1(sK2) != k1_relat_1(sK2) | v1_funct_2(sK2,k1_relat_1(sK2),sK1) | k1_xboole_0 = sK1 | ~sP0(k1_relat_1(sK2),sK2,sK1)),
% 1.57/0.56    inference(superposition,[],[f78,f150])).
% 1.57/0.56  fof(f150,plain,(
% 1.57/0.56    k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),sK1,sK2)),
% 1.57/0.56    inference(resolution,[],[f144,f52])).
% 1.57/0.56  fof(f144,plain,(
% 1.57/0.56    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),X0,sK2)) )),
% 1.57/0.56    inference(resolution,[],[f141,f75])).
% 1.57/0.56  fof(f75,plain,(
% 1.57/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f33])).
% 1.57/0.56  fof(f33,plain,(
% 1.57/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.56    inference(ennf_transformation,[],[f12])).
% 1.57/0.56  fof(f12,axiom,(
% 1.57/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.57/0.56  fof(f78,plain,(
% 1.57/0.56    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) != X0 | v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | ~sP0(X0,X1,X2)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f48])).
% 1.57/0.56  fof(f48,plain,(
% 1.57/0.56    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.57/0.56    inference(rectify,[],[f47])).
% 1.57/0.56  fof(f47,plain,(
% 1.57/0.56    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.57/0.56    inference(nnf_transformation,[],[f39])).
% 1.57/0.56  fof(f285,plain,(
% 1.57/0.56    r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),sK1),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))))),
% 1.57/0.56    inference(subsumption_resolution,[],[f277,f65])).
% 1.57/0.56  fof(f277,plain,(
% 1.57/0.56    r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),sK1),k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))) | ~v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))),
% 1.57/0.56    inference(superposition,[],[f55,f263])).
% 1.57/0.56  fof(f263,plain,(
% 1.57/0.56    k1_relat_1(sK2) = k1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))),
% 1.57/0.56    inference(resolution,[],[f228,f52])).
% 1.57/0.56  fof(f228,plain,(
% 1.57/0.56    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | k1_relat_1(sK2) = k1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) )),
% 1.57/0.56    inference(resolution,[],[f225,f146])).
% 1.57/0.56  fof(f146,plain,(
% 1.57/0.56    ( ! [X2] : (r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),X2)) | ~r1_tarski(k2_relat_1(sK2),X2)) )),
% 1.57/0.56    inference(resolution,[],[f141,f72])).
% 1.57/0.56  fof(f72,plain,(
% 1.57/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f46])).
% 1.57/0.56  fof(f46,plain,(
% 1.57/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.57/0.56    inference(nnf_transformation,[],[f4])).
% 1.57/0.56  fof(f4,axiom,(
% 1.57/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.57/0.56  fof(f225,plain,(
% 1.57/0.56    ( ! [X0] : (~r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),X0)) | k1_relat_1(sK2) = k1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) )),
% 1.57/0.56    inference(resolution,[],[f122,f50])).
% 1.57/0.56  fof(f122,plain,(
% 1.57/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),X1)) | k1_relat_1(X0) = k1_relat_1(k2_zfmisc_1(k1_relat_1(X0),X1))) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f121,f65])).
% 1.57/0.56  fof(f121,plain,(
% 1.57/0.56    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k2_zfmisc_1(k1_relat_1(X0),X1)) | ~r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),X1)) | ~v1_relat_1(k2_zfmisc_1(k1_relat_1(X0),X1)) | ~v1_relat_1(X0)) )),
% 1.57/0.56    inference(resolution,[],[f100,f60])).
% 1.57/0.56  fof(f60,plain,(
% 1.57/0.56    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f27])).
% 1.57/0.56  fof(f27,plain,(
% 1.57/0.56    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.57/0.56    inference(flattening,[],[f26])).
% 1.57/0.56  fof(f26,plain,(
% 1.57/0.56    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.57/0.56    inference(ennf_transformation,[],[f9])).
% 1.57/0.56  fof(f9,axiom,(
% 1.57/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 1.57/0.56  fof(f100,plain,(
% 1.57/0.56    ( ! [X4,X5] : (~r1_tarski(X4,k1_relat_1(k2_zfmisc_1(X4,X5))) | k1_relat_1(k2_zfmisc_1(X4,X5)) = X4) )),
% 1.57/0.56    inference(resolution,[],[f71,f67])).
% 1.57/0.56  fof(f67,plain,(
% 1.57/0.56    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f6])).
% 1.57/0.56  fof(f6,axiom,(
% 1.57/0.56    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).
% 1.57/0.56  fof(f55,plain,(
% 1.57/0.56    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f22])).
% 1.57/0.56  fof(f22,plain,(
% 1.57/0.56    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.57/0.56    inference(ennf_transformation,[],[f8])).
% 1.57/0.56  fof(f8,axiom,(
% 1.57/0.56    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 1.57/0.56  fof(f338,plain,(
% 1.57/0.56    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = k2_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))),
% 1.57/0.56    inference(subsumption_resolution,[],[f330,f65])).
% 1.57/0.56  fof(f330,plain,(
% 1.57/0.56    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = k2_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)) | ~v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))),
% 1.57/0.56    inference(superposition,[],[f58,f309])).
% 1.57/0.56  fof(f309,plain,(
% 1.57/0.56    k1_relat_1(sK2) = k1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))),
% 1.57/0.56    inference(backward_demodulation,[],[f263,f304])).
% 1.57/0.56  fof(f58,plain,(
% 1.57/0.56    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f43])).
% 1.57/0.56  fof(f43,plain,(
% 1.57/0.56    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.57/0.56    inference(nnf_transformation,[],[f25])).
% 1.57/0.56  fof(f25,plain,(
% 1.57/0.56    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.57/0.56    inference(ennf_transformation,[],[f11])).
% 1.57/0.56  fof(f11,axiom,(
% 1.57/0.56    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 1.57/0.56  fof(f503,plain,(
% 1.57/0.56    k2_relat_1(sK2) = k2_relat_1(k1_xboole_0)),
% 1.57/0.56    inference(forward_demodulation,[],[f467,f497])).
% 1.57/0.56  fof(f497,plain,(
% 1.57/0.56    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2))),
% 1.57/0.56    inference(global_subsumption,[],[f415,f447])).
% 1.57/0.56  fof(f447,plain,(
% 1.57/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.57/0.56    inference(forward_demodulation,[],[f446,f427])).
% 1.57/0.56  fof(f427,plain,(
% 1.57/0.56    k1_xboole_0 = k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)),
% 1.57/0.56    inference(backward_demodulation,[],[f376,f378])).
% 1.57/0.56  fof(f378,plain,(
% 1.57/0.56    k1_relat_1(sK2) = k1_relat_1(k1_xboole_0)),
% 1.57/0.56    inference(backward_demodulation,[],[f309,f376])).
% 1.57/0.56  fof(f446,plain,(
% 1.57/0.56    k1_xboole_0 = k1_relat_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))),
% 1.57/0.56    inference(forward_demodulation,[],[f445,f378])).
% 1.57/0.56  fof(f445,plain,(
% 1.57/0.56    k1_xboole_0 = k1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))),
% 1.57/0.56    inference(subsumption_resolution,[],[f372,f65])).
% 1.57/0.56  fof(f372,plain,(
% 1.57/0.56    k1_xboole_0 = k1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)) | ~v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))),
% 1.57/0.56    inference(trivial_inequality_removal,[],[f366])).
% 1.57/0.56  fof(f366,plain,(
% 1.57/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)) | ~v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))),
% 1.57/0.56    inference(superposition,[],[f59,f352])).
% 1.57/0.56  fof(f59,plain,(
% 1.57/0.56    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f43])).
% 1.57/0.56  fof(f415,plain,(
% 1.57/0.56    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2))),
% 1.57/0.56    inference(backward_demodulation,[],[f251,f378])).
% 1.57/0.56  fof(f251,plain,(
% 1.57/0.56    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2))),
% 1.57/0.56    inference(inner_rewriting,[],[f250])).
% 1.57/0.56  fof(f250,plain,(
% 1.57/0.56    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),
% 1.57/0.56    inference(subsumption_resolution,[],[f241,f65])).
% 1.57/0.56  fof(f241,plain,(
% 1.57/0.56    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))),
% 1.57/0.56    inference(superposition,[],[f56,f227])).
% 1.57/0.56  fof(f227,plain,(
% 1.57/0.56    k1_relat_1(sK2) = k1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))),
% 1.57/0.56    inference(resolution,[],[f225,f116])).
% 1.57/0.56  fof(f116,plain,(
% 1.57/0.56    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))),
% 1.57/0.56    inference(resolution,[],[f114,f72])).
% 1.57/0.56  fof(f114,plain,(
% 1.57/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 1.57/0.56    inference(subsumption_resolution,[],[f113,f50])).
% 1.57/0.56  fof(f113,plain,(
% 1.57/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_relat_1(sK2)),
% 1.57/0.56    inference(resolution,[],[f64,f51])).
% 1.57/0.56  fof(f64,plain,(
% 1.57/0.56    ( ! [X0] : (~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f29])).
% 1.57/0.56  fof(f29,plain,(
% 1.57/0.56    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.57/0.56    inference(flattening,[],[f28])).
% 1.57/0.56  fof(f28,plain,(
% 1.57/0.56    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.57/0.56    inference(ennf_transformation,[],[f17])).
% 1.57/0.56  fof(f17,axiom,(
% 1.57/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 1.57/0.56  fof(f56,plain,(
% 1.57/0.56    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f24])).
% 1.57/0.56  fof(f24,plain,(
% 1.57/0.56    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.57/0.56    inference(flattening,[],[f23])).
% 1.57/0.56  fof(f23,plain,(
% 1.57/0.56    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.57/0.56    inference(ennf_transformation,[],[f10])).
% 1.57/0.56  fof(f10,axiom,(
% 1.57/0.56    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.57/0.56  fof(f467,plain,(
% 1.57/0.56    k2_relat_1(sK2) = k2_relat_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2)))),
% 1.57/0.56    inference(backward_demodulation,[],[f400,f447])).
% 1.57/0.56  fof(f400,plain,(
% 1.57/0.56    k2_relat_1(sK2) = k2_relat_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(sK2)))),
% 1.57/0.56    inference(backward_demodulation,[],[f162,f378])).
% 1.57/0.56  fof(f162,plain,(
% 1.57/0.56    k2_relat_1(sK2) = k2_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))),
% 1.57/0.56    inference(resolution,[],[f160,f116])).
% 1.57/0.56  fof(f160,plain,(
% 1.57/0.56    ( ! [X0] : (~r1_tarski(sK2,k2_zfmisc_1(X0,k2_relat_1(sK2))) | k2_relat_1(sK2) = k2_relat_1(k2_zfmisc_1(X0,k2_relat_1(sK2)))) )),
% 1.57/0.56    inference(resolution,[],[f120,f50])).
% 1.57/0.56  fof(f120,plain,(
% 1.57/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) | k2_relat_1(X1) = k2_relat_1(k2_zfmisc_1(X0,k2_relat_1(X1)))) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f119,f65])).
% 1.57/0.56  fof(f119,plain,(
% 1.57/0.56    ( ! [X0,X1] : (k2_relat_1(X1) = k2_relat_1(k2_zfmisc_1(X0,k2_relat_1(X1))) | ~r1_tarski(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) | ~v1_relat_1(k2_zfmisc_1(X0,k2_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 1.57/0.56    inference(resolution,[],[f99,f61])).
% 1.57/0.56  fof(f61,plain,(
% 1.57/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f27])).
% 1.57/0.56  fof(f57,plain,(
% 1.57/0.56    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f24])).
% 1.57/0.56  fof(f51,plain,(
% 1.57/0.56    v1_funct_1(sK2)),
% 1.57/0.56    inference(cnf_transformation,[],[f42])).
% 1.57/0.56  fof(f562,plain,(
% 1.57/0.56    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0)),
% 1.57/0.56    inference(forward_demodulation,[],[f561,f449])).
% 1.57/0.56  fof(f449,plain,(
% 1.57/0.56    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),
% 1.57/0.56    inference(subsumption_resolution,[],[f423,f447])).
% 1.57/0.56  fof(f423,plain,(
% 1.57/0.56    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),
% 1.57/0.56    inference(backward_demodulation,[],[f311,f378])).
% 1.57/0.56  fof(f311,plain,(
% 1.57/0.56    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),
% 1.57/0.56    inference(backward_demodulation,[],[f287,f304])).
% 1.57/0.56  fof(f287,plain,(
% 1.57/0.56    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1)),
% 1.57/0.56    inference(inner_rewriting,[],[f286])).
% 1.57/0.56  fof(f286,plain,(
% 1.57/0.56    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = k2_zfmisc_1(k1_relat_1(sK2),sK1)),
% 1.57/0.56    inference(subsumption_resolution,[],[f278,f65])).
% 1.57/0.56  fof(f278,plain,(
% 1.57/0.56    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = k2_zfmisc_1(k1_relat_1(sK2),sK1) | ~v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))),
% 1.57/0.56    inference(superposition,[],[f56,f263])).
% 1.57/0.56  fof(f561,plain,(
% 1.57/0.56    v1_funct_2(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0)),
% 1.57/0.56    inference(forward_demodulation,[],[f560,f447])).
% 1.57/0.56  fof(f560,plain,(
% 1.57/0.56    v1_funct_2(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0),k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0)),
% 1.57/0.56    inference(forward_demodulation,[],[f559,f504])).
% 1.57/0.56  fof(f559,plain,(
% 1.57/0.56    ~v1_funct_1(k1_xboole_0) | v1_funct_2(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(sK2)),k1_relat_1(k1_xboole_0),k2_relat_1(sK2))),
% 1.57/0.56    inference(forward_demodulation,[],[f558,f449])).
% 1.57/0.56  fof(f558,plain,(
% 1.57/0.56    ~v1_funct_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | v1_funct_2(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(sK2)),k1_relat_1(k1_xboole_0),k2_relat_1(sK2))),
% 1.57/0.56    inference(forward_demodulation,[],[f488,f504])).
% 1.57/0.56  fof(f488,plain,(
% 1.57/0.56    ~v1_funct_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2))) | v1_funct_2(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(sK2)),k1_relat_1(k1_xboole_0),k2_relat_1(sK2))),
% 1.57/0.56    inference(backward_demodulation,[],[f435,f447])).
% 1.57/0.56  fof(f435,plain,(
% 1.57/0.56    v1_funct_2(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(sK2)),k1_relat_1(k1_xboole_0),k2_relat_1(sK2)) | ~v1_funct_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(sK2)))),
% 1.57/0.56    inference(forward_demodulation,[],[f413,f378])).
% 1.57/0.56  fof(f413,plain,(
% 1.57/0.56    ~v1_funct_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(sK2))) | v1_funct_2(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2))),
% 1.57/0.56    inference(backward_demodulation,[],[f231,f378])).
% 1.57/0.56  fof(f231,plain,(
% 1.57/0.56    v1_funct_2(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))),
% 1.57/0.56    inference(backward_demodulation,[],[f182,f227])).
% 1.57/0.56  fof(f182,plain,(
% 1.57/0.56    v1_funct_2(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_relat_1(sK2)) | ~v1_funct_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))),
% 1.57/0.56    inference(subsumption_resolution,[],[f172,f65])).
% 1.57/0.56  fof(f172,plain,(
% 1.57/0.56    v1_funct_2(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),k1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))),k2_relat_1(sK2)) | ~v1_funct_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) | ~v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))),
% 1.57/0.56    inference(superposition,[],[f63,f162])).
% 1.57/0.56  fof(f63,plain,(
% 1.57/0.56    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f29])).
% 1.57/0.56  fof(f635,plain,(
% 1.57/0.56    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.57/0.56    inference(backward_demodulation,[],[f570,f611])).
% 1.57/0.56  fof(f570,plain,(
% 1.57/0.56    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 1.57/0.56    inference(subsumption_resolution,[],[f494,f501])).
% 1.57/0.56  fof(f501,plain,(
% 1.57/0.56    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 1.57/0.56    inference(forward_demodulation,[],[f455,f497])).
% 1.57/0.56  fof(f455,plain,(
% 1.57/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2))))),
% 1.57/0.56    inference(backward_demodulation,[],[f385,f447])).
% 1.57/0.56  fof(f385,plain,(
% 1.57/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(sK2))))),
% 1.57/0.56    inference(backward_demodulation,[],[f114,f378])).
% 1.57/0.56  fof(f494,plain,(
% 1.57/0.56    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 1.57/0.56    inference(backward_demodulation,[],[f441,f447])).
% 1.57/0.56  fof(f441,plain,(
% 1.57/0.56    ~v1_funct_2(sK2,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 1.57/0.56    inference(forward_demodulation,[],[f381,f378])).
% 1.57/0.56  fof(f381,plain,(
% 1.57/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)),
% 1.57/0.56    inference(backward_demodulation,[],[f318,f376])).
% 1.57/0.56  fof(f318,plain,(
% 1.57/0.56    ~v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))),
% 1.57/0.56    inference(forward_demodulation,[],[f306,f304])).
% 1.57/0.56  fof(f306,plain,(
% 1.57/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) | ~v1_funct_2(sK2,k1_relat_1(sK2),sK1)),
% 1.57/0.56    inference(backward_demodulation,[],[f94,f304])).
% 1.57/0.56  % SZS output end Proof for theBenchmark
% 1.57/0.56  % (24519)------------------------------
% 1.57/0.56  % (24519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (24519)Termination reason: Refutation
% 1.57/0.56  
% 1.57/0.56  % (24519)Memory used [KB]: 6524
% 1.57/0.56  % (24519)Time elapsed: 0.156 s
% 1.57/0.56  % (24519)------------------------------
% 1.57/0.56  % (24519)------------------------------
% 1.57/0.56  % (24515)Success in time 0.206 s
%------------------------------------------------------------------------------
