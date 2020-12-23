%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:16 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 291 expanded)
%              Number of leaves         :   14 (  65 expanded)
%              Depth                    :   16
%              Number of atoms          :  260 ( 972 expanded)
%              Number of equality atoms :   80 ( 273 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f616,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f84,f169,f194,f613])).

fof(f613,plain,
    ( spl1_2
    | ~ spl1_8 ),
    inference(avatar_contradiction_clause,[],[f612])).

fof(f612,plain,
    ( $false
    | spl1_2
    | ~ spl1_8 ),
    inference(subsumption_resolution,[],[f611,f166])).

fof(f166,plain,(
    ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f164,f151])).

fof(f151,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f128,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f128,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    inference(resolution,[],[f107,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f107,plain,(
    ! [X0] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(superposition,[],[f99,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f99,plain,(
    ! [X0,X1] : m1_subset_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f96,f93])).

fof(f93,plain,(
    ! [X0,X1] : k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(resolution,[],[f41,f86])).

fof(f86,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f36,f49])).

fof(f49,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f96,plain,(
    ! [X0,X1] : m1_subset_1(k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f42,f86])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f164,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(superposition,[],[f102,f135])).

fof(f135,plain,(
    ! [X0] : k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f95,f86])).

fof(f95,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | k1_relset_1(k1_xboole_0,X2,X3) = k1_relat_1(X3) ) ),
    inference(superposition,[],[f41,f52])).

fof(f52,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f102,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X0,k1_xboole_0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(resolution,[],[f81,f86])).

fof(f81,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(forward_demodulation,[],[f56,f52])).

fof(f56,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f611,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl1_2
    | ~ spl1_8 ),
    inference(forward_demodulation,[],[f601,f151])).

fof(f601,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | spl1_2
    | ~ spl1_8 ),
    inference(superposition,[],[f207,f508])).

fof(f508,plain,
    ( k1_xboole_0 = sK0
    | ~ spl1_8 ),
    inference(resolution,[],[f291,f31])).

fof(f291,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl1_8 ),
    inference(resolution,[],[f209,f35])).

fof(f209,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl1_8 ),
    inference(forward_demodulation,[],[f206,f51])).

fof(f206,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)))
    | ~ spl1_8 ),
    inference(superposition,[],[f167,f185])).

fof(f185,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl1_8
  <=> k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f167,plain,(
    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    inference(resolution,[],[f149,f28])).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
      | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
      | ~ v1_funct_1(sK0) )
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          | ~ v1_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
        | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
        | ~ v1_funct_1(sK0) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f149,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(resolution,[],[f112,f49])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),X1)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f40,f49])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f207,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)
    | spl1_2
    | ~ spl1_8 ),
    inference(superposition,[],[f65,f185])).

fof(f65,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl1_2
  <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f194,plain,
    ( spl1_2
    | spl1_8 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | spl1_2
    | spl1_8 ),
    inference(global_subsumption,[],[f181,f179,f184])).

fof(f184,plain,
    ( k1_xboole_0 != k2_relat_1(sK0)
    | spl1_8 ),
    inference(avatar_component_clause,[],[f183])).

fof(f179,plain,(
    k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) ),
    inference(resolution,[],[f167,f41])).

fof(f181,plain,
    ( k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | k1_xboole_0 = k2_relat_1(sK0)
    | spl1_2 ),
    inference(subsumption_resolution,[],[f176,f65])).

fof(f176,plain,
    ( k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | k1_xboole_0 = k2_relat_1(sK0)
    | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(resolution,[],[f167,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f169,plain,(
    spl1_3 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | spl1_3 ),
    inference(subsumption_resolution,[],[f167,f69])).

fof(f69,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | spl1_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl1_3
  <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f84,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | spl1_1 ),
    inference(subsumption_resolution,[],[f61,f29])).

fof(f29,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,
    ( ~ v1_funct_1(sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl1_1
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f70,plain,
    ( ~ spl1_1
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f30,f67,f63,f59])).

fof(f30,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:25:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.37  ipcrm: permission denied for id (797769728)
% 0.21/0.37  ipcrm: permission denied for id (797802497)
% 0.21/0.37  ipcrm: permission denied for id (803831811)
% 0.21/0.37  ipcrm: permission denied for id (797835268)
% 0.21/0.37  ipcrm: permission denied for id (801505285)
% 0.21/0.37  ipcrm: permission denied for id (797868038)
% 0.21/0.38  ipcrm: permission denied for id (803864583)
% 0.21/0.38  ipcrm: permission denied for id (797900808)
% 0.21/0.38  ipcrm: permission denied for id (797933577)
% 0.21/0.38  ipcrm: permission denied for id (797966346)
% 0.21/0.38  ipcrm: permission denied for id (803897355)
% 0.21/0.38  ipcrm: permission denied for id (798031884)
% 0.21/0.38  ipcrm: permission denied for id (798097422)
% 0.21/0.39  ipcrm: permission denied for id (798130192)
% 0.21/0.39  ipcrm: permission denied for id (801701906)
% 0.21/0.39  ipcrm: permission denied for id (801734675)
% 0.21/0.39  ipcrm: permission denied for id (798228500)
% 0.21/0.39  ipcrm: permission denied for id (798261269)
% 0.21/0.39  ipcrm: permission denied for id (798294038)
% 0.21/0.40  ipcrm: permission denied for id (798326807)
% 0.21/0.40  ipcrm: permission denied for id (798359576)
% 0.21/0.40  ipcrm: permission denied for id (798392345)
% 0.21/0.40  ipcrm: permission denied for id (798425114)
% 0.21/0.40  ipcrm: permission denied for id (798457883)
% 0.21/0.40  ipcrm: permission denied for id (804061212)
% 0.21/0.40  ipcrm: permission denied for id (804093981)
% 0.21/0.40  ipcrm: permission denied for id (801832990)
% 0.21/0.41  ipcrm: permission denied for id (804126751)
% 0.21/0.41  ipcrm: permission denied for id (804159520)
% 0.21/0.41  ipcrm: permission denied for id (804192289)
% 0.21/0.41  ipcrm: permission denied for id (804257827)
% 0.21/0.41  ipcrm: permission denied for id (804290596)
% 0.21/0.41  ipcrm: permission denied for id (802095141)
% 0.21/0.41  ipcrm: permission denied for id (802127910)
% 0.21/0.42  ipcrm: permission denied for id (804323367)
% 0.21/0.42  ipcrm: permission denied for id (802193448)
% 0.21/0.42  ipcrm: permission denied for id (798720041)
% 0.21/0.42  ipcrm: permission denied for id (798752810)
% 0.21/0.42  ipcrm: permission denied for id (798785579)
% 0.21/0.42  ipcrm: permission denied for id (798818348)
% 0.21/0.42  ipcrm: permission denied for id (798851117)
% 0.21/0.42  ipcrm: permission denied for id (798883886)
% 0.21/0.43  ipcrm: permission denied for id (798916655)
% 0.21/0.43  ipcrm: permission denied for id (798982193)
% 0.21/0.43  ipcrm: permission denied for id (799047731)
% 0.21/0.43  ipcrm: permission denied for id (802291764)
% 0.21/0.43  ipcrm: permission denied for id (799113269)
% 0.21/0.43  ipcrm: permission denied for id (804421686)
% 0.21/0.44  ipcrm: permission denied for id (802357303)
% 0.21/0.44  ipcrm: permission denied for id (799211576)
% 0.21/0.44  ipcrm: permission denied for id (802422842)
% 0.21/0.44  ipcrm: permission denied for id (804487227)
% 0.21/0.44  ipcrm: permission denied for id (804519996)
% 0.21/0.45  ipcrm: permission denied for id (802586687)
% 0.21/0.45  ipcrm: permission denied for id (799473728)
% 0.21/0.45  ipcrm: permission denied for id (804618305)
% 0.21/0.45  ipcrm: permission denied for id (804651074)
% 0.21/0.45  ipcrm: permission denied for id (802717764)
% 0.21/0.45  ipcrm: permission denied for id (802750533)
% 0.21/0.45  ipcrm: permission denied for id (802783302)
% 0.21/0.46  ipcrm: permission denied for id (802816071)
% 0.21/0.46  ipcrm: permission denied for id (799703113)
% 0.21/0.46  ipcrm: permission denied for id (802881610)
% 0.21/0.46  ipcrm: permission denied for id (799768651)
% 0.21/0.46  ipcrm: permission denied for id (799834188)
% 0.21/0.46  ipcrm: permission denied for id (804749389)
% 0.21/0.46  ipcrm: permission denied for id (799899726)
% 0.21/0.47  ipcrm: permission denied for id (804782159)
% 0.21/0.47  ipcrm: permission denied for id (804814928)
% 0.21/0.47  ipcrm: permission denied for id (799998034)
% 0.21/0.47  ipcrm: permission denied for id (804880467)
% 0.21/0.47  ipcrm: permission denied for id (800063573)
% 0.21/0.47  ipcrm: permission denied for id (800096342)
% 0.21/0.48  ipcrm: permission denied for id (800129111)
% 0.21/0.48  ipcrm: permission denied for id (800194649)
% 0.21/0.48  ipcrm: permission denied for id (803143770)
% 0.21/0.48  ipcrm: permission denied for id (803176539)
% 0.21/0.48  ipcrm: permission denied for id (804978780)
% 0.21/0.48  ipcrm: permission denied for id (800325725)
% 0.21/0.49  ipcrm: permission denied for id (800391263)
% 0.21/0.49  ipcrm: permission denied for id (803274848)
% 0.21/0.49  ipcrm: permission denied for id (800456801)
% 0.21/0.49  ipcrm: permission denied for id (800489570)
% 0.21/0.49  ipcrm: permission denied for id (800555108)
% 0.21/0.49  ipcrm: permission denied for id (800587877)
% 0.21/0.49  ipcrm: permission denied for id (800620646)
% 0.21/0.50  ipcrm: permission denied for id (800653415)
% 0.21/0.50  ipcrm: permission denied for id (800718952)
% 0.21/0.50  ipcrm: permission denied for id (803340393)
% 0.21/0.50  ipcrm: permission denied for id (805077098)
% 0.21/0.50  ipcrm: permission denied for id (800817259)
% 0.21/0.50  ipcrm: permission denied for id (800850028)
% 0.21/0.50  ipcrm: permission denied for id (800882797)
% 0.21/0.51  ipcrm: permission denied for id (800981104)
% 0.21/0.51  ipcrm: permission denied for id (805175409)
% 0.21/0.51  ipcrm: permission denied for id (803504242)
% 0.21/0.51  ipcrm: permission denied for id (801144947)
% 0.21/0.51  ipcrm: permission denied for id (801177716)
% 0.21/0.51  ipcrm: permission denied for id (803537013)
% 0.21/0.51  ipcrm: permission denied for id (805208182)
% 0.21/0.52  ipcrm: permission denied for id (803602551)
% 0.21/0.52  ipcrm: permission denied for id (801243256)
% 0.21/0.52  ipcrm: permission denied for id (805240953)
% 0.21/0.52  ipcrm: permission denied for id (801276026)
% 0.21/0.52  ipcrm: permission denied for id (803668091)
% 0.21/0.52  ipcrm: permission denied for id (805273724)
% 0.21/0.52  ipcrm: permission denied for id (805306493)
% 0.21/0.52  ipcrm: permission denied for id (801374334)
% 0.21/0.53  ipcrm: permission denied for id (805339263)
% 0.46/0.61  % (10801)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.46/0.63  % (10801)Refutation found. Thanks to Tanya!
% 0.46/0.63  % SZS status Theorem for theBenchmark
% 0.46/0.64  % SZS output start Proof for theBenchmark
% 0.46/0.64  fof(f616,plain,(
% 0.46/0.64    $false),
% 0.46/0.64    inference(avatar_sat_refutation,[],[f70,f84,f169,f194,f613])).
% 0.46/0.64  fof(f613,plain,(
% 0.46/0.64    spl1_2 | ~spl1_8),
% 0.46/0.64    inference(avatar_contradiction_clause,[],[f612])).
% 0.46/0.64  fof(f612,plain,(
% 0.46/0.64    $false | (spl1_2 | ~spl1_8)),
% 0.46/0.64    inference(subsumption_resolution,[],[f611,f166])).
% 0.46/0.64  fof(f166,plain,(
% 0.46/0.64    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.46/0.64    inference(subsumption_resolution,[],[f164,f151])).
% 0.46/0.64  fof(f151,plain,(
% 0.46/0.64    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.46/0.64    inference(resolution,[],[f128,f31])).
% 0.46/0.64  fof(f31,plain,(
% 0.46/0.64    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.46/0.64    inference(cnf_transformation,[],[f13])).
% 0.46/0.64  fof(f13,plain,(
% 0.46/0.64    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.46/0.64    inference(ennf_transformation,[],[f2])).
% 0.46/0.64  fof(f2,axiom,(
% 0.46/0.64    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.46/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.46/0.64  fof(f128,plain,(
% 0.46/0.64    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) )),
% 0.46/0.64    inference(resolution,[],[f107,f35])).
% 0.46/0.64  fof(f35,plain,(
% 0.46/0.64    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.46/0.64    inference(cnf_transformation,[],[f24])).
% 0.46/0.64  fof(f24,plain,(
% 0.46/0.64    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.46/0.64    inference(nnf_transformation,[],[f4])).
% 0.46/0.64  fof(f4,axiom,(
% 0.46/0.64    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.46/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.46/0.64  fof(f107,plain,(
% 0.46/0.64    ( ! [X0] : (m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X0))) )),
% 0.46/0.64    inference(superposition,[],[f99,f51])).
% 0.46/0.64  fof(f51,plain,(
% 0.46/0.64    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.46/0.64    inference(equality_resolution,[],[f39])).
% 0.46/0.64  fof(f39,plain,(
% 0.46/0.64    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.46/0.64    inference(cnf_transformation,[],[f26])).
% 0.46/0.64  fof(f26,plain,(
% 0.46/0.64    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.46/0.64    inference(flattening,[],[f25])).
% 0.46/0.64  fof(f25,plain,(
% 0.46/0.64    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.46/0.64    inference(nnf_transformation,[],[f3])).
% 0.46/0.64  fof(f3,axiom,(
% 0.46/0.64    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.46/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.46/0.64  fof(f99,plain,(
% 0.46/0.64    ( ! [X0,X1] : (m1_subset_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k1_zfmisc_1(X0))) )),
% 0.46/0.64    inference(forward_demodulation,[],[f96,f93])).
% 0.46/0.64  fof(f93,plain,(
% 0.46/0.64    ( ! [X0,X1] : (k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.46/0.64    inference(resolution,[],[f41,f86])).
% 0.46/0.64  fof(f86,plain,(
% 0.46/0.64    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.46/0.64    inference(resolution,[],[f36,f49])).
% 0.46/0.64  fof(f49,plain,(
% 0.46/0.64    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.46/0.64    inference(equality_resolution,[],[f33])).
% 0.46/0.64  fof(f33,plain,(
% 0.46/0.64    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.46/0.64    inference(cnf_transformation,[],[f23])).
% 0.46/0.64  fof(f23,plain,(
% 0.46/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.46/0.64    inference(flattening,[],[f22])).
% 0.46/0.64  fof(f22,plain,(
% 0.46/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.46/0.64    inference(nnf_transformation,[],[f1])).
% 0.46/0.64  fof(f1,axiom,(
% 0.46/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.46/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.46/0.64  fof(f36,plain,(
% 0.46/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.46/0.64    inference(cnf_transformation,[],[f24])).
% 0.46/0.64  fof(f41,plain,(
% 0.46/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.46/0.64    inference(cnf_transformation,[],[f16])).
% 0.46/0.64  fof(f16,plain,(
% 0.46/0.64    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.46/0.64    inference(ennf_transformation,[],[f6])).
% 0.46/0.64  fof(f6,axiom,(
% 0.46/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.46/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.46/0.64  fof(f96,plain,(
% 0.46/0.64    ( ! [X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)),k1_zfmisc_1(X0))) )),
% 0.46/0.64    inference(resolution,[],[f42,f86])).
% 0.46/0.64  fof(f42,plain,(
% 0.46/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.46/0.64    inference(cnf_transformation,[],[f17])).
% 0.46/0.64  fof(f17,plain,(
% 0.46/0.64    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.46/0.64    inference(ennf_transformation,[],[f5])).
% 0.46/0.64  fof(f5,axiom,(
% 0.46/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.46/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.46/0.64  fof(f164,plain,(
% 0.46/0.64    ( ! [X0] : (k1_xboole_0 != k1_relat_1(k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.46/0.64    inference(superposition,[],[f102,f135])).
% 0.46/0.64  fof(f135,plain,(
% 0.46/0.64    ( ! [X0] : (k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_relat_1(k1_xboole_0)) )),
% 0.46/0.64    inference(resolution,[],[f95,f86])).
% 0.46/0.64  fof(f95,plain,(
% 0.46/0.64    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_relset_1(k1_xboole_0,X2,X3) = k1_relat_1(X3)) )),
% 0.46/0.64    inference(superposition,[],[f41,f52])).
% 0.46/0.64  fof(f52,plain,(
% 0.46/0.64    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.46/0.64    inference(equality_resolution,[],[f38])).
% 0.46/0.64  fof(f38,plain,(
% 0.46/0.64    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.46/0.64    inference(cnf_transformation,[],[f26])).
% 0.46/0.64  fof(f102,plain,(
% 0.46/0.64    ( ! [X0] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X0,k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.46/0.64    inference(resolution,[],[f81,f86])).
% 0.46/0.64  fof(f81,plain,(
% 0.46/0.64    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.46/0.64    inference(forward_demodulation,[],[f56,f52])).
% 0.46/0.64  fof(f56,plain,(
% 0.46/0.64    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.46/0.64    inference(equality_resolution,[],[f46])).
% 0.79/0.64  fof(f46,plain,(
% 0.79/0.64    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.79/0.64    inference(cnf_transformation,[],[f27])).
% 0.79/0.64  fof(f27,plain,(
% 0.79/0.64    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.79/0.64    inference(nnf_transformation,[],[f19])).
% 0.79/0.64  fof(f19,plain,(
% 0.79/0.64    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.79/0.64    inference(flattening,[],[f18])).
% 0.79/0.64  fof(f18,plain,(
% 0.79/0.64    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.79/0.64    inference(ennf_transformation,[],[f8])).
% 0.79/0.64  fof(f8,axiom,(
% 0.79/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.79/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.79/0.64  fof(f611,plain,(
% 0.79/0.64    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl1_2 | ~spl1_8)),
% 0.79/0.64    inference(forward_demodulation,[],[f601,f151])).
% 0.79/0.64  fof(f601,plain,(
% 0.79/0.64    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (spl1_2 | ~spl1_8)),
% 0.79/0.64    inference(superposition,[],[f207,f508])).
% 0.79/0.64  fof(f508,plain,(
% 0.79/0.64    k1_xboole_0 = sK0 | ~spl1_8),
% 0.79/0.64    inference(resolution,[],[f291,f31])).
% 0.79/0.64  fof(f291,plain,(
% 0.79/0.64    r1_tarski(sK0,k1_xboole_0) | ~spl1_8),
% 0.79/0.64    inference(resolution,[],[f209,f35])).
% 0.79/0.64  fof(f209,plain,(
% 0.79/0.64    m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) | ~spl1_8),
% 0.79/0.64    inference(forward_demodulation,[],[f206,f51])).
% 0.79/0.64  fof(f206,plain,(
% 0.79/0.64    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) | ~spl1_8),
% 0.79/0.64    inference(superposition,[],[f167,f185])).
% 0.79/0.64  fof(f185,plain,(
% 0.79/0.64    k1_xboole_0 = k2_relat_1(sK0) | ~spl1_8),
% 0.79/0.64    inference(avatar_component_clause,[],[f183])).
% 0.79/0.64  fof(f183,plain,(
% 0.79/0.64    spl1_8 <=> k1_xboole_0 = k2_relat_1(sK0)),
% 0.79/0.64    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.79/0.64  fof(f167,plain,(
% 0.79/0.64    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.79/0.64    inference(resolution,[],[f149,f28])).
% 0.79/0.64  fof(f28,plain,(
% 0.79/0.64    v1_relat_1(sK0)),
% 0.79/0.64    inference(cnf_transformation,[],[f21])).
% 0.79/0.64  fof(f21,plain,(
% 0.79/0.64    (~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.79/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f20])).
% 0.79/0.64  fof(f20,plain,(
% 0.79/0.64    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.79/0.64    introduced(choice_axiom,[])).
% 0.79/0.64  fof(f12,plain,(
% 0.79/0.64    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.79/0.64    inference(flattening,[],[f11])).
% 0.79/0.64  fof(f11,plain,(
% 0.79/0.64    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.79/0.64    inference(ennf_transformation,[],[f10])).
% 0.79/0.64  fof(f10,negated_conjecture,(
% 0.79/0.64    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.79/0.64    inference(negated_conjecture,[],[f9])).
% 0.79/0.64  fof(f9,conjecture,(
% 0.79/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.79/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.79/0.64  fof(f149,plain,(
% 0.79/0.64    ( ! [X0] : (~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.79/0.64    inference(resolution,[],[f112,f49])).
% 0.79/0.64  fof(f112,plain,(
% 0.79/0.64    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),X1) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 0.79/0.64    inference(resolution,[],[f40,f49])).
% 0.79/0.64  fof(f40,plain,(
% 0.79/0.64    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.79/0.64    inference(cnf_transformation,[],[f15])).
% 0.79/0.64  fof(f15,plain,(
% 0.79/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.79/0.64    inference(flattening,[],[f14])).
% 0.79/0.64  fof(f14,plain,(
% 0.79/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.79/0.64    inference(ennf_transformation,[],[f7])).
% 0.79/0.64  fof(f7,axiom,(
% 0.79/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.79/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.79/0.64  fof(f207,plain,(
% 0.79/0.64    ~v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) | (spl1_2 | ~spl1_8)),
% 0.79/0.64    inference(superposition,[],[f65,f185])).
% 0.79/0.64  fof(f65,plain,(
% 0.79/0.64    ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | spl1_2),
% 0.79/0.64    inference(avatar_component_clause,[],[f63])).
% 0.79/0.64  fof(f63,plain,(
% 0.79/0.64    spl1_2 <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.79/0.64    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.79/0.64  fof(f194,plain,(
% 0.79/0.64    spl1_2 | spl1_8),
% 0.79/0.64    inference(avatar_contradiction_clause,[],[f193])).
% 0.79/0.64  fof(f193,plain,(
% 0.79/0.64    $false | (spl1_2 | spl1_8)),
% 0.79/0.64    inference(global_subsumption,[],[f181,f179,f184])).
% 0.79/0.64  fof(f184,plain,(
% 0.79/0.64    k1_xboole_0 != k2_relat_1(sK0) | spl1_8),
% 0.79/0.64    inference(avatar_component_clause,[],[f183])).
% 0.79/0.64  fof(f179,plain,(
% 0.79/0.64    k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)),
% 0.79/0.64    inference(resolution,[],[f167,f41])).
% 0.79/0.64  fof(f181,plain,(
% 0.79/0.64    k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | k1_xboole_0 = k2_relat_1(sK0) | spl1_2),
% 0.79/0.64    inference(subsumption_resolution,[],[f176,f65])).
% 0.79/0.64  fof(f176,plain,(
% 0.79/0.64    k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | k1_xboole_0 = k2_relat_1(sK0) | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.79/0.64    inference(resolution,[],[f167,f45])).
% 0.79/0.64  fof(f45,plain,(
% 0.79/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | v1_funct_2(X2,X0,X1)) )),
% 0.79/0.64    inference(cnf_transformation,[],[f27])).
% 0.79/0.64  fof(f169,plain,(
% 0.79/0.64    spl1_3),
% 0.79/0.64    inference(avatar_contradiction_clause,[],[f168])).
% 0.79/0.64  fof(f168,plain,(
% 0.79/0.64    $false | spl1_3),
% 0.79/0.64    inference(subsumption_resolution,[],[f167,f69])).
% 0.79/0.64  fof(f69,plain,(
% 0.79/0.64    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | spl1_3),
% 0.79/0.64    inference(avatar_component_clause,[],[f67])).
% 0.79/0.64  fof(f67,plain,(
% 0.79/0.64    spl1_3 <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.79/0.64    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.79/0.64  fof(f84,plain,(
% 0.79/0.64    spl1_1),
% 0.79/0.64    inference(avatar_contradiction_clause,[],[f83])).
% 0.79/0.64  fof(f83,plain,(
% 0.79/0.64    $false | spl1_1),
% 0.79/0.64    inference(subsumption_resolution,[],[f61,f29])).
% 0.79/0.64  fof(f29,plain,(
% 0.79/0.64    v1_funct_1(sK0)),
% 0.79/0.64    inference(cnf_transformation,[],[f21])).
% 0.79/0.64  fof(f61,plain,(
% 0.79/0.64    ~v1_funct_1(sK0) | spl1_1),
% 0.79/0.64    inference(avatar_component_clause,[],[f59])).
% 0.79/0.64  fof(f59,plain,(
% 0.79/0.64    spl1_1 <=> v1_funct_1(sK0)),
% 0.79/0.64    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.79/0.64  fof(f70,plain,(
% 0.79/0.64    ~spl1_1 | ~spl1_2 | ~spl1_3),
% 0.79/0.64    inference(avatar_split_clause,[],[f30,f67,f63,f59])).
% 0.79/0.64  fof(f30,plain,(
% 0.79/0.64    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)),
% 0.79/0.64    inference(cnf_transformation,[],[f21])).
% 0.79/0.64  % SZS output end Proof for theBenchmark
% 0.79/0.64  % (10801)------------------------------
% 0.79/0.64  % (10801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.79/0.64  % (10801)Termination reason: Refutation
% 0.79/0.64  
% 0.79/0.64  % (10801)Memory used [KB]: 10874
% 0.79/0.64  % (10801)Time elapsed: 0.047 s
% 0.79/0.64  % (10801)------------------------------
% 0.79/0.64  % (10801)------------------------------
% 0.79/0.64  % (10636)Success in time 0.279 s
%------------------------------------------------------------------------------
