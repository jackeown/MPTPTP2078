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
% DateTime   : Thu Dec  3 13:00:21 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 512 expanded)
%              Number of leaves         :   25 ( 129 expanded)
%              Depth                    :   18
%              Number of atoms          :  391 (1845 expanded)
%              Number of equality atoms :   93 ( 293 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f418,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f110,f201,f212,f266,f396,f417])).

fof(f417,plain,
    ( spl3_2
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f416])).

fof(f416,plain,
    ( $false
    | spl3_2
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(global_subsumption,[],[f409,f415])).

fof(f415,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f414,f269])).

fof(f269,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f268,f243])).

fof(f243,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f242])).

fof(f242,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f135,f112])).

fof(f112,plain,(
    ! [X0] : k1_xboole_0 = k2_relat_1(k2_zfmisc_1(X0,k1_xboole_0)) ),
    inference(resolution,[],[f69,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f69,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).

fof(f135,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k2_relat_1(k2_zfmisc_1(X1,X2))
      | k1_xboole_0 = k2_zfmisc_1(X1,X2) ) ),
    inference(resolution,[],[f59,f68])).

fof(f68,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f268,plain,(
    ! [X0] : k1_xboole_0 = k1_relat_1(k2_zfmisc_1(X0,k1_xboole_0)) ),
    inference(trivial_inequality_removal,[],[f267])).

fof(f267,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = k1_relat_1(k2_zfmisc_1(X0,k1_xboole_0)) ) ),
    inference(superposition,[],[f156,f112])).

fof(f156,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k2_relat_1(k2_zfmisc_1(X1,X2))
      | k1_xboole_0 = k1_relat_1(k2_zfmisc_1(X1,X2)) ) ),
    inference(resolution,[],[f61,f68])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f414,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f207,f382])).

fof(f382,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_13 ),
    inference(resolution,[],[f323,f64])).

fof(f323,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f322,f243])).

fof(f322,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k1_zfmisc_1(k3_tarski(k1_relat_1(sK1))),k1_xboole_0))
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f303,f255])).

fof(f255,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl3_13
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f303,plain,(
    r1_tarski(sK1,k2_zfmisc_1(k1_zfmisc_1(k3_tarski(k1_relat_1(sK1))),sK0)) ),
    inference(resolution,[],[f199,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f199,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_zfmisc_1(k3_tarski(k1_relat_1(sK1))),sK0))) ),
    inference(resolution,[],[f192,f56])).

fof(f56,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f192,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK1),X0)
      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) ) ),
    inference(subsumption_resolution,[],[f187,f52])).

fof(f52,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
      | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
      | ~ v1_funct_1(sK1) )
    & r1_tarski(k2_relat_1(sK1),sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f42])).

fof(f42,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
        | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
        | ~ v1_funct_1(sK1) )
      & r1_tarski(k2_relat_1(sK1),sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f187,plain,(
    ! [X0] :
      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | ~ r1_tarski(k1_relat_1(sK1),X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f79,f54])).

fof(f54,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f207,plain,
    ( v1_xboole_0(k1_relat_1(sK1))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl3_11
  <=> v1_xboole_0(k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f409,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_2
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f408,f269])).

fof(f408,plain,
    ( ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
    | spl3_2
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f407,f382])).

fof(f407,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK1))
    | spl3_2 ),
    inference(subsumption_resolution,[],[f249,f262])).

fof(f262,plain,
    ( ~ v1_partfun1(sK1,k1_relat_1(sK1))
    | spl3_2 ),
    inference(subsumption_resolution,[],[f261,f103])).

fof(f103,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl3_2
  <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f261,plain,
    ( ~ v1_partfun1(sK1,k1_relat_1(sK1))
    | v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    inference(subsumption_resolution,[],[f247,f53])).

fof(f53,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f247,plain,
    ( ~ v1_partfun1(sK1,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    inference(resolution,[],[f198,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f198,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    inference(resolution,[],[f192,f89])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f249,plain,
    ( v1_partfun1(sK1,k1_relat_1(sK1))
    | ~ v1_xboole_0(k1_relat_1(sK1)) ),
    inference(resolution,[],[f198,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f396,plain,
    ( spl3_12
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f395])).

fof(f395,plain,
    ( $false
    | spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f394,f211])).

fof(f211,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_xboole_0)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl3_12
  <=> r1_tarski(k1_relat_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f394,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_xboole_0)
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f393,f269])).

fof(f393,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_relat_1(k1_xboole_0))
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f392,f52])).

fof(f392,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK1)
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f384,f338])).

fof(f338,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f68,f243])).

fof(f384,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK1)
    | ~ spl3_13 ),
    inference(resolution,[],[f323,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f266,plain,
    ( spl3_2
    | spl3_13 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | spl3_2
    | spl3_13 ),
    inference(global_subsumption,[],[f251,f248,f254])).

% (27308)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% (27288)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% (27288)Refutation not found, incomplete strategy% (27288)------------------------------
% (27288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27284)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% (27288)Termination reason: Refutation not found, incomplete strategy

% (27288)Memory used [KB]: 6140
% (27288)Time elapsed: 0.103 s
% (27288)------------------------------
% (27288)------------------------------
% (27295)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% (27296)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% (27303)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% (27305)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% (27307)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% (27304)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% (27291)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% (27297)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (27306)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
fof(f254,plain,
    ( k1_xboole_0 != sK0
    | spl3_13 ),
    inference(avatar_component_clause,[],[f253])).

fof(f248,plain,(
    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1) ),
    inference(resolution,[],[f198,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f251,plain,
    ( k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | k1_xboole_0 = sK0
    | spl3_2 ),
    inference(subsumption_resolution,[],[f245,f103])).

fof(f245,plain,
    ( k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | k1_xboole_0 = sK0
    | v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    inference(resolution,[],[f198,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f212,plain,
    ( spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f203,f209,f205])).

fof(f203,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_xboole_0)
    | v1_xboole_0(k1_relat_1(sK1)) ),
    inference(resolution,[],[f197,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f197,plain,(
    r1_xboole_0(k1_relat_1(sK1),k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f196])).

fof(f196,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK1),k1_xboole_0) ),
    inference(superposition,[],[f158,f114])).

fof(f114,plain,(
    k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0) ),
    inference(resolution,[],[f57,f52])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

fof(f158,plain,(
    ! [X0] :
      ( k1_xboole_0 != k9_relat_1(sK1,X0)
      | r1_xboole_0(k1_relat_1(sK1),X0) ) ),
    inference(resolution,[],[f72,f52])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 != k9_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(f201,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f198,f107])).

fof(f107,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f110,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f99,f53])).

fof(f99,plain,
    ( ~ v1_funct_1(sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl3_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f108,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f55,f105,f101,f97])).

fof(f55,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_vampire %s %d
% 0.12/0.31  % Computer   : n021.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 19:19:49 EST 2020
% 0.16/0.31  % CPUTime    : 
% 0.17/0.43  % (27285)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.17/0.44  % (27287)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.17/0.44  % (27302)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.17/0.45  % (27283)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.17/0.45  % (27294)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.17/0.46  % (27299)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.17/0.46  % (27292)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.17/0.47  % (27298)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.17/0.47  % (27293)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.17/0.47  % (27290)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.17/0.48  % (27286)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.17/0.48  % (27293)Refutation found. Thanks to Tanya!
% 0.17/0.48  % SZS status Theorem for theBenchmark
% 0.17/0.48  % SZS output start Proof for theBenchmark
% 0.17/0.48  fof(f418,plain,(
% 0.17/0.48    $false),
% 0.17/0.48    inference(avatar_sat_refutation,[],[f108,f110,f201,f212,f266,f396,f417])).
% 0.17/0.48  fof(f417,plain,(
% 0.17/0.48    spl3_2 | ~spl3_11 | ~spl3_13),
% 0.17/0.48    inference(avatar_contradiction_clause,[],[f416])).
% 0.17/0.48  fof(f416,plain,(
% 0.17/0.48    $false | (spl3_2 | ~spl3_11 | ~spl3_13)),
% 0.17/0.48    inference(global_subsumption,[],[f409,f415])).
% 0.17/0.48  fof(f415,plain,(
% 0.17/0.48    v1_xboole_0(k1_xboole_0) | (~spl3_11 | ~spl3_13)),
% 0.17/0.48    inference(forward_demodulation,[],[f414,f269])).
% 0.17/0.48  fof(f269,plain,(
% 0.17/0.48    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.17/0.48    inference(forward_demodulation,[],[f268,f243])).
% 0.17/0.48  fof(f243,plain,(
% 0.17/0.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.17/0.48    inference(trivial_inequality_removal,[],[f242])).
% 0.17/0.48  fof(f242,plain,(
% 0.17/0.48    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.17/0.48    inference(superposition,[],[f135,f112])).
% 0.17/0.48  fof(f112,plain,(
% 0.17/0.48    ( ! [X0] : (k1_xboole_0 = k2_relat_1(k2_zfmisc_1(X0,k1_xboole_0))) )),
% 0.17/0.48    inference(resolution,[],[f69,f64])).
% 0.17/0.48  fof(f64,plain,(
% 0.17/0.48    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.17/0.48    inference(cnf_transformation,[],[f30])).
% 0.17/0.48  fof(f30,plain,(
% 0.17/0.48    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.17/0.48    inference(ennf_transformation,[],[f2])).
% 0.17/0.48  fof(f2,axiom,(
% 0.17/0.48    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.17/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.17/0.48  fof(f69,plain,(
% 0.17/0.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)) )),
% 0.17/0.48    inference(cnf_transformation,[],[f9])).
% 0.17/0.48  fof(f9,axiom,(
% 0.17/0.48    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)),
% 0.17/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).
% 0.17/0.48  fof(f135,plain,(
% 0.17/0.48    ( ! [X2,X1] : (k1_xboole_0 != k2_relat_1(k2_zfmisc_1(X1,X2)) | k1_xboole_0 = k2_zfmisc_1(X1,X2)) )),
% 0.17/0.48    inference(resolution,[],[f59,f68])).
% 0.17/0.48  fof(f68,plain,(
% 0.17/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.17/0.48    inference(cnf_transformation,[],[f6])).
% 0.17/0.48  fof(f6,axiom,(
% 0.17/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.17/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.17/0.48  fof(f59,plain,(
% 0.17/0.48    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.17/0.48    inference(cnf_transformation,[],[f26])).
% 0.17/0.48  fof(f26,plain,(
% 0.17/0.48    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.17/0.48    inference(flattening,[],[f25])).
% 0.17/0.48  fof(f25,plain,(
% 0.17/0.48    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.17/0.48    inference(ennf_transformation,[],[f11])).
% 0.17/0.48  fof(f11,axiom,(
% 0.17/0.48    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.17/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.17/0.48  fof(f268,plain,(
% 0.17/0.48    ( ! [X0] : (k1_xboole_0 = k1_relat_1(k2_zfmisc_1(X0,k1_xboole_0))) )),
% 0.17/0.48    inference(trivial_inequality_removal,[],[f267])).
% 0.17/0.48  fof(f267,plain,(
% 0.17/0.48    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_relat_1(k2_zfmisc_1(X0,k1_xboole_0))) )),
% 0.17/0.48    inference(superposition,[],[f156,f112])).
% 0.17/0.48  fof(f156,plain,(
% 0.17/0.48    ( ! [X2,X1] : (k1_xboole_0 != k2_relat_1(k2_zfmisc_1(X1,X2)) | k1_xboole_0 = k1_relat_1(k2_zfmisc_1(X1,X2))) )),
% 0.17/0.48    inference(resolution,[],[f61,f68])).
% 0.17/0.48  fof(f61,plain,(
% 0.17/0.48    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 0.17/0.48    inference(cnf_transformation,[],[f44])).
% 0.17/0.48  fof(f44,plain,(
% 0.17/0.48    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.17/0.48    inference(nnf_transformation,[],[f27])).
% 0.17/0.48  fof(f27,plain,(
% 0.17/0.48    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.17/0.48    inference(ennf_transformation,[],[f12])).
% 0.17/0.48  fof(f12,axiom,(
% 0.17/0.48    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.17/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.17/0.48  fof(f414,plain,(
% 0.17/0.48    v1_xboole_0(k1_relat_1(k1_xboole_0)) | (~spl3_11 | ~spl3_13)),
% 0.17/0.48    inference(forward_demodulation,[],[f207,f382])).
% 0.17/0.48  fof(f382,plain,(
% 0.17/0.48    k1_xboole_0 = sK1 | ~spl3_13),
% 0.17/0.48    inference(resolution,[],[f323,f64])).
% 0.17/0.48  fof(f323,plain,(
% 0.17/0.48    r1_tarski(sK1,k1_xboole_0) | ~spl3_13),
% 0.17/0.48    inference(forward_demodulation,[],[f322,f243])).
% 0.17/0.48  fof(f322,plain,(
% 0.17/0.48    r1_tarski(sK1,k2_zfmisc_1(k1_zfmisc_1(k3_tarski(k1_relat_1(sK1))),k1_xboole_0)) | ~spl3_13),
% 0.17/0.48    inference(forward_demodulation,[],[f303,f255])).
% 0.17/0.48  fof(f255,plain,(
% 0.17/0.48    k1_xboole_0 = sK0 | ~spl3_13),
% 0.17/0.48    inference(avatar_component_clause,[],[f253])).
% 0.17/0.48  fof(f253,plain,(
% 0.17/0.48    spl3_13 <=> k1_xboole_0 = sK0),
% 0.17/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.17/0.48  fof(f303,plain,(
% 0.17/0.48    r1_tarski(sK1,k2_zfmisc_1(k1_zfmisc_1(k3_tarski(k1_relat_1(sK1))),sK0))),
% 0.17/0.48    inference(resolution,[],[f199,f77])).
% 0.17/0.48  fof(f77,plain,(
% 0.17/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.17/0.48    inference(cnf_transformation,[],[f50])).
% 0.17/0.48  fof(f50,plain,(
% 0.17/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.17/0.48    inference(nnf_transformation,[],[f5])).
% 0.17/0.48  fof(f5,axiom,(
% 0.17/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.17/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.17/0.48  fof(f199,plain,(
% 0.17/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_zfmisc_1(k3_tarski(k1_relat_1(sK1))),sK0)))),
% 0.17/0.48    inference(resolution,[],[f192,f56])).
% 0.17/0.48  fof(f56,plain,(
% 0.17/0.48    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 0.17/0.48    inference(cnf_transformation,[],[f4])).
% 0.17/0.48  fof(f4,axiom,(
% 0.17/0.48    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 0.17/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 0.17/0.48  fof(f192,plain,(
% 0.17/0.48    ( ! [X0] : (~r1_tarski(k1_relat_1(sK1),X0) | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) )),
% 0.17/0.48    inference(subsumption_resolution,[],[f187,f52])).
% 0.17/0.48  fof(f52,plain,(
% 0.17/0.48    v1_relat_1(sK1)),
% 0.17/0.48    inference(cnf_transformation,[],[f43])).
% 0.17/0.48  fof(f43,plain,(
% 0.17/0.48    (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.17/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f42])).
% 0.17/0.48  fof(f42,plain,(
% 0.17/0.48    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.17/0.48    introduced(choice_axiom,[])).
% 0.17/0.48  fof(f23,plain,(
% 0.17/0.48    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.17/0.48    inference(flattening,[],[f22])).
% 0.17/0.48  fof(f22,plain,(
% 0.17/0.48    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.17/0.48    inference(ennf_transformation,[],[f20])).
% 0.17/0.48  fof(f20,negated_conjecture,(
% 0.17/0.48    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.17/0.48    inference(negated_conjecture,[],[f19])).
% 0.17/0.48  fof(f19,conjecture,(
% 0.17/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.17/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.17/0.48  fof(f187,plain,(
% 0.17/0.48    ( ! [X0] : (m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~r1_tarski(k1_relat_1(sK1),X0) | ~v1_relat_1(sK1)) )),
% 0.17/0.48    inference(resolution,[],[f79,f54])).
% 0.17/0.48  fof(f54,plain,(
% 0.17/0.48    r1_tarski(k2_relat_1(sK1),sK0)),
% 0.17/0.48    inference(cnf_transformation,[],[f43])).
% 0.17/0.48  fof(f79,plain,(
% 0.17/0.48    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.17/0.48    inference(cnf_transformation,[],[f36])).
% 0.17/0.48  fof(f36,plain,(
% 0.17/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.17/0.48    inference(flattening,[],[f35])).
% 0.17/0.48  fof(f35,plain,(
% 0.17/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.17/0.48    inference(ennf_transformation,[],[f15])).
% 0.17/0.48  fof(f15,axiom,(
% 0.17/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.17/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.17/0.48  fof(f207,plain,(
% 0.17/0.48    v1_xboole_0(k1_relat_1(sK1)) | ~spl3_11),
% 0.17/0.48    inference(avatar_component_clause,[],[f205])).
% 0.17/0.48  fof(f205,plain,(
% 0.17/0.48    spl3_11 <=> v1_xboole_0(k1_relat_1(sK1))),
% 0.17/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.17/0.48  fof(f409,plain,(
% 0.17/0.48    ~v1_xboole_0(k1_xboole_0) | (spl3_2 | ~spl3_13)),
% 0.17/0.48    inference(forward_demodulation,[],[f408,f269])).
% 0.17/0.48  fof(f408,plain,(
% 0.17/0.48    ~v1_xboole_0(k1_relat_1(k1_xboole_0)) | (spl3_2 | ~spl3_13)),
% 0.17/0.48    inference(forward_demodulation,[],[f407,f382])).
% 0.17/0.48  fof(f407,plain,(
% 0.17/0.48    ~v1_xboole_0(k1_relat_1(sK1)) | spl3_2),
% 0.17/0.48    inference(subsumption_resolution,[],[f249,f262])).
% 0.17/0.48  fof(f262,plain,(
% 0.17/0.48    ~v1_partfun1(sK1,k1_relat_1(sK1)) | spl3_2),
% 0.17/0.48    inference(subsumption_resolution,[],[f261,f103])).
% 0.17/0.48  fof(f103,plain,(
% 0.17/0.48    ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | spl3_2),
% 0.17/0.48    inference(avatar_component_clause,[],[f101])).
% 0.17/0.48  fof(f101,plain,(
% 0.17/0.48    spl3_2 <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0)),
% 0.17/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.17/0.48  fof(f261,plain,(
% 0.17/0.48    ~v1_partfun1(sK1,k1_relat_1(sK1)) | v1_funct_2(sK1,k1_relat_1(sK1),sK0)),
% 0.17/0.48    inference(subsumption_resolution,[],[f247,f53])).
% 0.17/0.48  fof(f53,plain,(
% 0.17/0.48    v1_funct_1(sK1)),
% 0.17/0.48    inference(cnf_transformation,[],[f43])).
% 0.17/0.48  fof(f247,plain,(
% 0.17/0.48    ~v1_partfun1(sK1,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | v1_funct_2(sK1,k1_relat_1(sK1),sK0)),
% 0.17/0.48    inference(resolution,[],[f198,f88])).
% 0.17/0.48  fof(f88,plain,(
% 0.17/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | v1_funct_2(X2,X0,X1)) )),
% 0.17/0.48    inference(cnf_transformation,[],[f41])).
% 0.17/0.48  fof(f41,plain,(
% 0.17/0.48    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.48    inference(flattening,[],[f40])).
% 0.17/0.48  fof(f40,plain,(
% 0.17/0.48    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.48    inference(ennf_transformation,[],[f16])).
% 0.17/0.48  fof(f16,axiom,(
% 0.17/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.17/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).
% 0.17/0.48  fof(f198,plain,(
% 0.17/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))),
% 0.17/0.48    inference(resolution,[],[f192,f89])).
% 0.17/0.48  fof(f89,plain,(
% 0.17/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.17/0.48    inference(equality_resolution,[],[f75])).
% 0.17/0.48  fof(f75,plain,(
% 0.17/0.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.17/0.48    inference(cnf_transformation,[],[f49])).
% 0.17/0.48  fof(f49,plain,(
% 0.17/0.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.17/0.48    inference(flattening,[],[f48])).
% 0.17/0.48  fof(f48,plain,(
% 0.17/0.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.17/0.48    inference(nnf_transformation,[],[f1])).
% 0.17/0.48  fof(f1,axiom,(
% 0.17/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.17/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.17/0.48  fof(f249,plain,(
% 0.17/0.48    v1_partfun1(sK1,k1_relat_1(sK1)) | ~v1_xboole_0(k1_relat_1(sK1))),
% 0.17/0.48    inference(resolution,[],[f198,f71])).
% 0.17/0.48  fof(f71,plain,(
% 0.17/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.17/0.48    inference(cnf_transformation,[],[f33])).
% 0.17/0.48  fof(f33,plain,(
% 0.17/0.48    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.17/0.48    inference(ennf_transformation,[],[f17])).
% 0.17/0.48  fof(f17,axiom,(
% 0.17/0.48    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 0.17/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).
% 0.17/0.48  fof(f396,plain,(
% 0.17/0.48    spl3_12 | ~spl3_13),
% 0.17/0.48    inference(avatar_contradiction_clause,[],[f395])).
% 0.17/0.48  fof(f395,plain,(
% 0.17/0.48    $false | (spl3_12 | ~spl3_13)),
% 0.17/0.48    inference(subsumption_resolution,[],[f394,f211])).
% 0.17/0.48  fof(f211,plain,(
% 0.17/0.48    ~r1_tarski(k1_relat_1(sK1),k1_xboole_0) | spl3_12),
% 0.17/0.48    inference(avatar_component_clause,[],[f209])).
% 0.17/0.48  fof(f209,plain,(
% 0.17/0.48    spl3_12 <=> r1_tarski(k1_relat_1(sK1),k1_xboole_0)),
% 0.17/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.17/0.48  fof(f394,plain,(
% 0.17/0.48    r1_tarski(k1_relat_1(sK1),k1_xboole_0) | ~spl3_13),
% 0.17/0.48    inference(forward_demodulation,[],[f393,f269])).
% 0.17/0.48  fof(f393,plain,(
% 0.17/0.48    r1_tarski(k1_relat_1(sK1),k1_relat_1(k1_xboole_0)) | ~spl3_13),
% 0.17/0.48    inference(subsumption_resolution,[],[f392,f52])).
% 0.17/0.48  fof(f392,plain,(
% 0.17/0.48    r1_tarski(k1_relat_1(sK1),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(sK1) | ~spl3_13),
% 0.17/0.48    inference(subsumption_resolution,[],[f384,f338])).
% 0.17/0.48  fof(f338,plain,(
% 0.17/0.48    v1_relat_1(k1_xboole_0)),
% 0.17/0.48    inference(superposition,[],[f68,f243])).
% 0.17/0.48  fof(f384,plain,(
% 0.17/0.48    r1_tarski(k1_relat_1(sK1),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK1) | ~spl3_13),
% 0.17/0.48    inference(resolution,[],[f323,f62])).
% 0.17/0.48  fof(f62,plain,(
% 0.17/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.17/0.48    inference(cnf_transformation,[],[f29])).
% 0.17/0.48  fof(f29,plain,(
% 0.17/0.48    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.17/0.48    inference(flattening,[],[f28])).
% 0.17/0.48  fof(f28,plain,(
% 0.17/0.48    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.17/0.48    inference(ennf_transformation,[],[f10])).
% 0.17/0.48  fof(f10,axiom,(
% 0.17/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.17/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.17/0.48  fof(f266,plain,(
% 0.17/0.48    spl3_2 | spl3_13),
% 0.17/0.48    inference(avatar_contradiction_clause,[],[f265])).
% 0.17/0.48  fof(f265,plain,(
% 0.17/0.48    $false | (spl3_2 | spl3_13)),
% 0.17/0.48    inference(global_subsumption,[],[f251,f248,f254])).
% 0.17/0.48  % (27308)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.17/0.48  % (27288)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.17/0.48  % (27288)Refutation not found, incomplete strategy% (27288)------------------------------
% 0.17/0.48  % (27288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.49  % (27284)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.17/0.49  % (27288)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.49  
% 0.17/0.49  % (27288)Memory used [KB]: 6140
% 0.17/0.49  % (27288)Time elapsed: 0.103 s
% 0.17/0.49  % (27288)------------------------------
% 0.17/0.49  % (27288)------------------------------
% 0.17/0.49  % (27295)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.17/0.49  % (27296)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.17/0.49  % (27303)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.17/0.49  % (27305)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.17/0.49  % (27307)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.17/0.50  % (27304)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.17/0.50  % (27291)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.17/0.50  % (27297)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.17/0.50  % (27306)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.17/0.50  fof(f254,plain,(
% 0.17/0.50    k1_xboole_0 != sK0 | spl3_13),
% 0.17/0.50    inference(avatar_component_clause,[],[f253])).
% 0.17/0.50  fof(f248,plain,(
% 0.17/0.50    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1)),
% 0.17/0.50    inference(resolution,[],[f198,f80])).
% 0.17/0.50  fof(f80,plain,(
% 0.17/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.17/0.50    inference(cnf_transformation,[],[f37])).
% 0.17/0.50  fof(f37,plain,(
% 0.17/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.50    inference(ennf_transformation,[],[f14])).
% 0.17/0.50  fof(f14,axiom,(
% 0.17/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.17/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.17/0.50  fof(f251,plain,(
% 0.17/0.50    k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1) | k1_xboole_0 = sK0 | spl3_2),
% 0.17/0.50    inference(subsumption_resolution,[],[f245,f103])).
% 0.17/0.50  fof(f245,plain,(
% 0.17/0.50    k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1) | k1_xboole_0 = sK0 | v1_funct_2(sK1,k1_relat_1(sK1),sK0)),
% 0.17/0.50    inference(resolution,[],[f198,f83])).
% 0.17/0.50  fof(f83,plain,(
% 0.17/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | v1_funct_2(X2,X0,X1)) )),
% 0.17/0.50    inference(cnf_transformation,[],[f51])).
% 0.17/0.50  fof(f51,plain,(
% 0.17/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.50    inference(nnf_transformation,[],[f39])).
% 0.17/0.50  fof(f39,plain,(
% 0.17/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.50    inference(flattening,[],[f38])).
% 0.17/0.50  fof(f38,plain,(
% 0.17/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.50    inference(ennf_transformation,[],[f18])).
% 0.17/0.50  fof(f18,axiom,(
% 0.17/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.17/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.17/0.50  fof(f212,plain,(
% 0.17/0.50    spl3_11 | ~spl3_12),
% 0.17/0.50    inference(avatar_split_clause,[],[f203,f209,f205])).
% 0.17/0.50  fof(f203,plain,(
% 0.17/0.50    ~r1_tarski(k1_relat_1(sK1),k1_xboole_0) | v1_xboole_0(k1_relat_1(sK1))),
% 0.17/0.50    inference(resolution,[],[f197,f70])).
% 0.17/0.50  fof(f70,plain,(
% 0.17/0.50    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.17/0.50    inference(cnf_transformation,[],[f32])).
% 0.17/0.50  fof(f32,plain,(
% 0.17/0.50    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.17/0.50    inference(flattening,[],[f31])).
% 0.17/0.50  fof(f31,plain,(
% 0.17/0.50    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.17/0.50    inference(ennf_transformation,[],[f3])).
% 0.17/0.50  fof(f3,axiom,(
% 0.17/0.50    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.17/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.17/0.50  fof(f197,plain,(
% 0.17/0.50    r1_xboole_0(k1_relat_1(sK1),k1_xboole_0)),
% 0.17/0.50    inference(trivial_inequality_removal,[],[f196])).
% 0.17/0.50  fof(f196,plain,(
% 0.17/0.50    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK1),k1_xboole_0)),
% 0.17/0.50    inference(superposition,[],[f158,f114])).
% 0.17/0.50  fof(f114,plain,(
% 0.17/0.50    k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0)),
% 0.17/0.50    inference(resolution,[],[f57,f52])).
% 0.17/0.50  fof(f57,plain,(
% 0.17/0.50    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)) )),
% 0.17/0.50    inference(cnf_transformation,[],[f24])).
% 0.17/0.50  fof(f24,plain,(
% 0.17/0.50    ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.17/0.50    inference(ennf_transformation,[],[f7])).
% 0.17/0.50  fof(f7,axiom,(
% 0.17/0.50    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 0.17/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).
% 0.17/0.50  fof(f158,plain,(
% 0.17/0.50    ( ! [X0] : (k1_xboole_0 != k9_relat_1(sK1,X0) | r1_xboole_0(k1_relat_1(sK1),X0)) )),
% 0.17/0.50    inference(resolution,[],[f72,f52])).
% 0.17/0.50  fof(f72,plain,(
% 0.17/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 != k9_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0)) )),
% 0.17/0.50    inference(cnf_transformation,[],[f47])).
% 0.17/0.50  fof(f47,plain,(
% 0.17/0.50    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.17/0.50    inference(nnf_transformation,[],[f34])).
% 0.17/0.50  fof(f34,plain,(
% 0.17/0.50    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.17/0.50    inference(ennf_transformation,[],[f8])).
% 0.17/0.50  fof(f8,axiom,(
% 0.17/0.50    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.17/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).
% 0.17/0.50  fof(f201,plain,(
% 0.17/0.50    spl3_3),
% 0.17/0.50    inference(avatar_contradiction_clause,[],[f200])).
% 0.17/0.50  fof(f200,plain,(
% 0.17/0.50    $false | spl3_3),
% 0.17/0.50    inference(subsumption_resolution,[],[f198,f107])).
% 0.17/0.50  fof(f107,plain,(
% 0.17/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | spl3_3),
% 0.17/0.50    inference(avatar_component_clause,[],[f105])).
% 0.17/0.50  fof(f105,plain,(
% 0.17/0.50    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))),
% 0.17/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.17/0.50  fof(f110,plain,(
% 0.17/0.50    spl3_1),
% 0.17/0.50    inference(avatar_contradiction_clause,[],[f109])).
% 0.17/0.50  fof(f109,plain,(
% 0.17/0.50    $false | spl3_1),
% 0.17/0.50    inference(subsumption_resolution,[],[f99,f53])).
% 0.17/0.50  fof(f99,plain,(
% 0.17/0.50    ~v1_funct_1(sK1) | spl3_1),
% 0.17/0.50    inference(avatar_component_clause,[],[f97])).
% 0.17/0.50  fof(f97,plain,(
% 0.17/0.50    spl3_1 <=> v1_funct_1(sK1)),
% 0.17/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.17/0.50  fof(f108,plain,(
% 0.17/0.50    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.17/0.50    inference(avatar_split_clause,[],[f55,f105,f101,f97])).
% 0.17/0.50  fof(f55,plain,(
% 0.17/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)),
% 0.17/0.50    inference(cnf_transformation,[],[f43])).
% 0.17/0.50  % SZS output end Proof for theBenchmark
% 0.17/0.50  % (27293)------------------------------
% 0.17/0.50  % (27293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.50  % (27293)Termination reason: Refutation
% 0.17/0.50  
% 0.17/0.50  % (27293)Memory used [KB]: 10874
% 0.17/0.50  % (27293)Time elapsed: 0.116 s
% 0.17/0.50  % (27293)------------------------------
% 0.17/0.50  % (27293)------------------------------
% 0.17/0.50  % (27281)Success in time 0.176 s
%------------------------------------------------------------------------------
