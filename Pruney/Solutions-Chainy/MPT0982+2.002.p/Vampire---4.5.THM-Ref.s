%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:26 EST 2020

% Result     : Theorem 1.69s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 715 expanded)
%              Number of leaves         :   19 ( 217 expanded)
%              Depth                    :   18
%              Number of atoms          :  454 (5560 expanded)
%              Number of equality atoms :  135 (1705 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f765,plain,(
    $false ),
    inference(subsumption_resolution,[],[f764,f147])).

fof(f147,plain,(
    ~ r1_tarski(sK2,k2_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f146,f97])).

fof(f97,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f76,f55])).

fof(f55,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( sK2 != k2_relset_1(sK1,sK2,sK4)
    & k1_xboole_0 != sK3
    & v2_funct_1(sK5)
    & sK3 = k2_relset_1(sK1,sK3,k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK5,sK2,sK3)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f20,f45,f44])).

fof(f44,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k2_relset_1(X0,X1,X3) != X1
            & k1_xboole_0 != X2
            & v2_funct_1(X4)
            & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( sK2 != k2_relset_1(sK1,sK2,sK4)
          & k1_xboole_0 != sK3
          & v2_funct_1(X4)
          & sK3 = k2_relset_1(sK1,sK3,k1_partfun1(sK1,sK2,sK2,sK3,sK4,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
          & v1_funct_2(X4,sK2,sK3)
          & v1_funct_1(X4) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X4] :
        ( sK2 != k2_relset_1(sK1,sK2,sK4)
        & k1_xboole_0 != sK3
        & v2_funct_1(X4)
        & sK3 = k2_relset_1(sK1,sK3,k1_partfun1(sK1,sK2,sK2,sK3,sK4,X4))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        & v1_funct_2(X4,sK2,sK3)
        & v1_funct_1(X4) )
   => ( sK2 != k2_relset_1(sK1,sK2,sK4)
      & k1_xboole_0 != sK3
      & v2_funct_1(sK5)
      & sK3 = k2_relset_1(sK1,sK3,k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5))
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK5,sK2,sK3)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( v2_funct_1(X4)
                & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
             => ( k2_relset_1(X0,X1,X3) = X1
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( v2_funct_1(X4)
              & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
           => ( k2_relset_1(X0,X1,X3) = X1
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f146,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f144,f143])).

fof(f143,plain,(
    sK2 != k2_relat_1(sK4) ),
    inference(superposition,[],[f62,f141])).

fof(f141,plain,(
    k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(resolution,[],[f78,f55])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f62,plain,(
    sK2 != k2_relset_1(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f144,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ r1_tarski(sK2,k2_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f99,f100])).

fof(f100,plain,(
    v5_relat_1(sK4,sK2) ),
    inference(resolution,[],[f79,f55])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f75,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
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

fof(f764,plain,(
    r1_tarski(sK2,k2_relat_1(sK4)) ),
    inference(forward_demodulation,[],[f760,f662])).

fof(f662,plain,(
    sK2 = k9_relat_1(k2_funct_1(sK5),sK3) ),
    inference(backward_demodulation,[],[f233,f640])).

fof(f640,plain,(
    sK3 = k2_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f148,f635])).

fof(f635,plain,(
    r1_tarski(sK3,k2_relat_1(sK5)) ),
    inference(backward_demodulation,[],[f122,f634])).

fof(f634,plain,(
    sK3 = k9_relat_1(sK5,k2_relat_1(sK4)) ),
    inference(backward_demodulation,[],[f111,f633])).

fof(f633,plain,(
    sK3 = k2_relat_1(k5_relat_1(sK4,sK5)) ),
    inference(forward_demodulation,[],[f617,f469])).

fof(f469,plain,(
    sK3 = k2_relset_1(sK1,sK3,k5_relat_1(sK4,sK5)) ),
    inference(backward_demodulation,[],[f59,f468])).

fof(f468,plain,(
    k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(subsumption_resolution,[],[f459,f56])).

fof(f56,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f459,plain,
    ( ~ v1_funct_1(sK5)
    | k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(resolution,[],[f318,f58])).

fof(f58,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f46])).

fof(f318,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k5_relat_1(sK4,X0) = k1_partfun1(sK1,sK2,X1,X2,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f316,f53])).

fof(f53,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f316,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k5_relat_1(sK4,X0) = k1_partfun1(sK1,sK2,X1,X2,sK4,X0)
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f87,f55])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f59,plain,(
    sK3 = k2_relset_1(sK1,sK3,k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f46])).

fof(f617,plain,(
    k2_relat_1(k5_relat_1(sK4,sK5)) = k2_relset_1(sK1,sK3,k5_relat_1(sK4,sK5)) ),
    inference(resolution,[],[f543,f78])).

fof(f543,plain,(
    m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(forward_demodulation,[],[f542,f468])).

fof(f542,plain,(
    m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(subsumption_resolution,[],[f539,f56])).

fof(f539,plain,
    ( ~ v1_funct_1(sK5)
    | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(resolution,[],[f373,f58])).

fof(f373,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | m1_subset_1(k1_partfun1(sK1,sK2,X1,X2,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) ) ),
    inference(subsumption_resolution,[],[f371,f53])).

% (17964)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f371,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | m1_subset_1(k1_partfun1(sK1,sK2,X1,X2,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f89,f55])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f111,plain,(
    k2_relat_1(k5_relat_1(sK4,sK5)) = k9_relat_1(sK5,k2_relat_1(sK4)) ),
    inference(resolution,[],[f107,f98])).

fof(f98,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f76,f58])).

fof(f107,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | k2_relat_1(k5_relat_1(sK4,X2)) = k9_relat_1(X2,k2_relat_1(sK4)) ) ),
    inference(resolution,[],[f64,f97])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f122,plain,(
    r1_tarski(k9_relat_1(sK5,k2_relat_1(sK4)),k2_relat_1(sK5)) ),
    inference(subsumption_resolution,[],[f121,f97])).

fof(f121,plain,
    ( r1_tarski(k9_relat_1(sK5,k2_relat_1(sK4)),k2_relat_1(sK5))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f118,f98])).

fof(f118,plain,
    ( r1_tarski(k9_relat_1(sK5,k2_relat_1(sK4)),k2_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4) ),
    inference(superposition,[],[f63,f111])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f148,plain,
    ( ~ r1_tarski(sK3,k2_relat_1(sK5))
    | sK3 = k2_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f145,f98])).

fof(f145,plain,
    ( sK3 = k2_relat_1(sK5)
    | ~ r1_tarski(sK3,k2_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f99,f101])).

fof(f101,plain,(
    v5_relat_1(sK5,sK3) ),
    inference(resolution,[],[f79,f58])).

fof(f233,plain,(
    sK2 = k9_relat_1(k2_funct_1(sK5),k2_relat_1(sK5)) ),
    inference(backward_demodulation,[],[f210,f225])).

fof(f225,plain,(
    sK2 = k1_relat_1(sK5) ),
    inference(backward_demodulation,[],[f140,f224])).

fof(f224,plain,(
    sK2 = k1_relset_1(sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f223,f61])).

fof(f61,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f46])).

fof(f223,plain,
    ( k1_xboole_0 = sK3
    | sK2 = k1_relset_1(sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f221,f57])).

fof(f57,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f221,plain,
    ( ~ v1_funct_2(sK5,sK2,sK3)
    | k1_xboole_0 = sK3
    | sK2 = k1_relset_1(sK2,sK3,sK5) ),
    inference(resolution,[],[f80,f103])).

fof(f103,plain,(
    sP0(sK2,sK5,sK3) ),
    inference(resolution,[],[f84,f58])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f37,f42])).

fof(f42,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f140,plain,(
    k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
    inference(resolution,[],[f77,f58])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f210,plain,(
    k1_relat_1(sK5) = k9_relat_1(k2_funct_1(sK5),k2_relat_1(sK5)) ),
    inference(forward_demodulation,[],[f209,f154])).

fof(f154,plain,(
    k1_relat_1(sK5) = k2_relat_1(k5_relat_1(sK5,k2_funct_1(sK5))) ),
    inference(subsumption_resolution,[],[f153,f98])).

fof(f153,plain,
    ( k1_relat_1(sK5) = k2_relat_1(k5_relat_1(sK5,k2_funct_1(sK5)))
    | ~ v1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f152,f56])).

fof(f152,plain,
    ( k1_relat_1(sK5) = k2_relat_1(k5_relat_1(sK5,k2_funct_1(sK5)))
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f68,f60])).

fof(f60,plain,(
    v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

fof(f209,plain,(
    k2_relat_1(k5_relat_1(sK5,k2_funct_1(sK5))) = k9_relat_1(k2_funct_1(sK5),k2_relat_1(sK5)) ),
    inference(subsumption_resolution,[],[f206,f98])).

fof(f206,plain,
    ( k2_relat_1(k5_relat_1(sK5,k2_funct_1(sK5))) = k9_relat_1(k2_funct_1(sK5),k2_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f124,f56])).

fof(f124,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k2_relat_1(k5_relat_1(sK5,k2_funct_1(X0))) = k9_relat_1(k2_funct_1(X0),k2_relat_1(sK5))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f108,f65])).

fof(f65,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f108,plain,(
    ! [X3] :
      ( ~ v1_relat_1(X3)
      | k2_relat_1(k5_relat_1(sK5,X3)) = k9_relat_1(X3,k2_relat_1(sK5)) ) ),
    inference(resolution,[],[f64,f98])).

fof(f760,plain,(
    r1_tarski(k9_relat_1(k2_funct_1(sK5),sK3),k2_relat_1(sK4)) ),
    inference(superposition,[],[f173,f634])).

fof(f173,plain,(
    ! [X0] : r1_tarski(k9_relat_1(k2_funct_1(sK5),k9_relat_1(sK5,X0)),X0) ),
    inference(subsumption_resolution,[],[f172,f98])).

fof(f172,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(k2_funct_1(sK5),k9_relat_1(sK5,X0)),X0)
      | ~ v1_relat_1(sK5) ) ),
    inference(subsumption_resolution,[],[f171,f56])).

fof(f171,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(k2_funct_1(sK5),k9_relat_1(sK5,X0)),X0)
      | ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5) ) ),
    inference(resolution,[],[f170,f65])).

fof(f170,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k2_funct_1(sK5))
      | r1_tarski(k9_relat_1(k2_funct_1(sK5),k9_relat_1(sK5,X0)),X0) ) ),
    inference(subsumption_resolution,[],[f169,f98])).

fof(f169,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(k2_funct_1(sK5),k9_relat_1(sK5,X0)),X0)
      | ~ v1_relat_1(k2_funct_1(sK5))
      | ~ v1_relat_1(sK5) ) ),
    inference(subsumption_resolution,[],[f168,f56])).

fof(f168,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(k2_funct_1(sK5),k9_relat_1(sK5,X0)),X0)
      | ~ v1_relat_1(k2_funct_1(sK5))
      | ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5) ) ),
    inference(resolution,[],[f167,f66])).

fof(f66,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f167,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k2_funct_1(sK5))
      | r1_tarski(k9_relat_1(k2_funct_1(sK5),k9_relat_1(sK5,X0)),X0)
      | ~ v1_relat_1(k2_funct_1(sK5)) ) ),
    inference(superposition,[],[f71,f166])).

fof(f166,plain,(
    ! [X0] : k9_relat_1(sK5,X0) = k10_relat_1(k2_funct_1(sK5),X0) ),
    inference(subsumption_resolution,[],[f165,f98])).

fof(f165,plain,(
    ! [X0] :
      ( k9_relat_1(sK5,X0) = k10_relat_1(k2_funct_1(sK5),X0)
      | ~ v1_relat_1(sK5) ) ),
    inference(subsumption_resolution,[],[f164,f56])).

fof(f164,plain,(
    ! [X0] :
      ( k9_relat_1(sK5,X0) = k10_relat_1(k2_funct_1(sK5),X0)
      | ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5) ) ),
    inference(resolution,[],[f72,f60])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (17960)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (17977)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (17970)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (17962)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (17963)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.54  % (17966)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.54  % (17967)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.54  % (17965)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.54  % (17972)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.55  % (17974)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.55  % (17968)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.55  % (17961)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.45/0.55  % (17981)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.45/0.55  % (17978)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.45/0.55  % (17959)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.45/0.56  % (17971)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.45/0.56  % (17957)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.45/0.56  % (17958)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.45/0.57  % (17980)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.45/0.57  % (17975)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.69/0.58  % (17973)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.69/0.58  % (17960)Refutation found. Thanks to Tanya!
% 1.69/0.58  % SZS status Theorem for theBenchmark
% 1.69/0.58  % (17976)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.69/0.58  % (17982)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.69/0.59  % SZS output start Proof for theBenchmark
% 1.69/0.59  fof(f765,plain,(
% 1.69/0.59    $false),
% 1.69/0.59    inference(subsumption_resolution,[],[f764,f147])).
% 1.69/0.59  fof(f147,plain,(
% 1.69/0.59    ~r1_tarski(sK2,k2_relat_1(sK4))),
% 1.69/0.59    inference(subsumption_resolution,[],[f146,f97])).
% 1.69/0.59  fof(f97,plain,(
% 1.69/0.59    v1_relat_1(sK4)),
% 1.69/0.59    inference(resolution,[],[f76,f55])).
% 1.69/0.59  fof(f55,plain,(
% 1.69/0.59    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.69/0.59    inference(cnf_transformation,[],[f46])).
% 1.69/0.59  fof(f46,plain,(
% 1.69/0.59    (sK2 != k2_relset_1(sK1,sK2,sK4) & k1_xboole_0 != sK3 & v2_funct_1(sK5) & sK3 = k2_relset_1(sK1,sK3,k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 1.69/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f20,f45,f44])).
% 1.69/0.59  fof(f44,plain,(
% 1.69/0.59    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (sK2 != k2_relset_1(sK1,sK2,sK4) & k1_xboole_0 != sK3 & v2_funct_1(X4) & sK3 = k2_relset_1(sK1,sK3,k1_partfun1(sK1,sK2,sK2,sK3,sK4,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X4,sK2,sK3) & v1_funct_1(X4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 1.69/0.59    introduced(choice_axiom,[])).
% 1.69/0.59  fof(f45,plain,(
% 1.69/0.59    ? [X4] : (sK2 != k2_relset_1(sK1,sK2,sK4) & k1_xboole_0 != sK3 & v2_funct_1(X4) & sK3 = k2_relset_1(sK1,sK3,k1_partfun1(sK1,sK2,sK2,sK3,sK4,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X4,sK2,sK3) & v1_funct_1(X4)) => (sK2 != k2_relset_1(sK1,sK2,sK4) & k1_xboole_0 != sK3 & v2_funct_1(sK5) & sK3 = k2_relset_1(sK1,sK3,k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5))),
% 1.69/0.59    introduced(choice_axiom,[])).
% 1.69/0.59  fof(f20,plain,(
% 1.69/0.59    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.69/0.59    inference(flattening,[],[f19])).
% 1.69/0.59  fof(f19,plain,(
% 1.69/0.59    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.69/0.59    inference(ennf_transformation,[],[f17])).
% 1.69/0.59  fof(f17,negated_conjecture,(
% 1.69/0.59    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 1.69/0.59    inference(negated_conjecture,[],[f16])).
% 1.69/0.59  fof(f16,conjecture,(
% 1.69/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).
% 1.69/0.59  fof(f76,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f32])).
% 1.69/0.59  fof(f32,plain,(
% 1.69/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.59    inference(ennf_transformation,[],[f9])).
% 1.69/0.59  fof(f9,axiom,(
% 1.69/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.69/0.59  fof(f146,plain,(
% 1.69/0.59    ~r1_tarski(sK2,k2_relat_1(sK4)) | ~v1_relat_1(sK4)),
% 1.69/0.59    inference(subsumption_resolution,[],[f144,f143])).
% 1.69/0.59  fof(f143,plain,(
% 1.69/0.59    sK2 != k2_relat_1(sK4)),
% 1.69/0.59    inference(superposition,[],[f62,f141])).
% 1.69/0.59  fof(f141,plain,(
% 1.69/0.59    k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4)),
% 1.69/0.59    inference(resolution,[],[f78,f55])).
% 1.69/0.59  fof(f78,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f34])).
% 1.69/0.59  fof(f34,plain,(
% 1.69/0.59    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.59    inference(ennf_transformation,[],[f12])).
% 1.69/0.59  fof(f12,axiom,(
% 1.69/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.69/0.59  fof(f62,plain,(
% 1.69/0.59    sK2 != k2_relset_1(sK1,sK2,sK4)),
% 1.69/0.59    inference(cnf_transformation,[],[f46])).
% 1.69/0.59  fof(f144,plain,(
% 1.69/0.59    sK2 = k2_relat_1(sK4) | ~r1_tarski(sK2,k2_relat_1(sK4)) | ~v1_relat_1(sK4)),
% 1.69/0.59    inference(resolution,[],[f99,f100])).
% 1.69/0.59  fof(f100,plain,(
% 1.69/0.59    v5_relat_1(sK4,sK2)),
% 1.69/0.59    inference(resolution,[],[f79,f55])).
% 1.69/0.59  fof(f79,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f35])).
% 1.69/0.59  fof(f35,plain,(
% 1.69/0.59    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.59    inference(ennf_transformation,[],[f18])).
% 1.69/0.59  fof(f18,plain,(
% 1.69/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.69/0.59    inference(pure_predicate_removal,[],[f10])).
% 1.69/0.59  fof(f10,axiom,(
% 1.69/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.69/0.59  fof(f99,plain,(
% 1.69/0.59    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | k2_relat_1(X1) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.69/0.59    inference(resolution,[],[f75,f69])).
% 1.69/0.59  fof(f69,plain,(
% 1.69/0.59    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f47])).
% 1.69/0.59  fof(f47,plain,(
% 1.69/0.59    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.69/0.59    inference(nnf_transformation,[],[f27])).
% 1.69/0.59  fof(f27,plain,(
% 1.69/0.59    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.69/0.59    inference(ennf_transformation,[],[f2])).
% 1.69/0.59  fof(f2,axiom,(
% 1.69/0.59    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.69/0.59  fof(f75,plain,(
% 1.69/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.69/0.59    inference(cnf_transformation,[],[f49])).
% 1.69/0.59  fof(f49,plain,(
% 1.69/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.69/0.59    inference(flattening,[],[f48])).
% 1.69/0.59  fof(f48,plain,(
% 1.69/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.69/0.59    inference(nnf_transformation,[],[f1])).
% 1.69/0.59  fof(f1,axiom,(
% 1.69/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.69/0.59  fof(f764,plain,(
% 1.69/0.59    r1_tarski(sK2,k2_relat_1(sK4))),
% 1.69/0.59    inference(forward_demodulation,[],[f760,f662])).
% 1.69/0.59  fof(f662,plain,(
% 1.69/0.59    sK2 = k9_relat_1(k2_funct_1(sK5),sK3)),
% 1.69/0.59    inference(backward_demodulation,[],[f233,f640])).
% 1.69/0.59  fof(f640,plain,(
% 1.69/0.59    sK3 = k2_relat_1(sK5)),
% 1.69/0.59    inference(subsumption_resolution,[],[f148,f635])).
% 1.69/0.59  fof(f635,plain,(
% 1.69/0.59    r1_tarski(sK3,k2_relat_1(sK5))),
% 1.69/0.59    inference(backward_demodulation,[],[f122,f634])).
% 1.69/0.59  fof(f634,plain,(
% 1.69/0.59    sK3 = k9_relat_1(sK5,k2_relat_1(sK4))),
% 1.69/0.59    inference(backward_demodulation,[],[f111,f633])).
% 1.69/0.59  fof(f633,plain,(
% 1.69/0.59    sK3 = k2_relat_1(k5_relat_1(sK4,sK5))),
% 1.69/0.59    inference(forward_demodulation,[],[f617,f469])).
% 1.69/0.59  fof(f469,plain,(
% 1.69/0.59    sK3 = k2_relset_1(sK1,sK3,k5_relat_1(sK4,sK5))),
% 1.69/0.59    inference(backward_demodulation,[],[f59,f468])).
% 1.69/0.59  fof(f468,plain,(
% 1.69/0.59    k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5) = k5_relat_1(sK4,sK5)),
% 1.69/0.59    inference(subsumption_resolution,[],[f459,f56])).
% 1.69/0.59  fof(f56,plain,(
% 1.69/0.59    v1_funct_1(sK5)),
% 1.69/0.59    inference(cnf_transformation,[],[f46])).
% 1.69/0.59  fof(f459,plain,(
% 1.69/0.59    ~v1_funct_1(sK5) | k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5) = k5_relat_1(sK4,sK5)),
% 1.69/0.59    inference(resolution,[],[f318,f58])).
% 1.69/0.59  fof(f58,plain,(
% 1.69/0.59    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 1.69/0.59    inference(cnf_transformation,[],[f46])).
% 1.69/0.59  fof(f318,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k5_relat_1(sK4,X0) = k1_partfun1(sK1,sK2,X1,X2,sK4,X0)) )),
% 1.69/0.59    inference(subsumption_resolution,[],[f316,f53])).
% 1.69/0.59  fof(f53,plain,(
% 1.69/0.59    v1_funct_1(sK4)),
% 1.69/0.59    inference(cnf_transformation,[],[f46])).
% 1.69/0.59  fof(f316,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k5_relat_1(sK4,X0) = k1_partfun1(sK1,sK2,X1,X2,sK4,X0) | ~v1_funct_1(sK4)) )),
% 1.69/0.59    inference(resolution,[],[f87,f55])).
% 1.69/0.59  fof(f87,plain,(
% 1.69/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X4)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f39])).
% 1.69/0.59  fof(f39,plain,(
% 1.69/0.59    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.69/0.59    inference(flattening,[],[f38])).
% 1.69/0.59  fof(f38,plain,(
% 1.69/0.59    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.69/0.59    inference(ennf_transformation,[],[f15])).
% 1.69/0.59  fof(f15,axiom,(
% 1.69/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.69/0.59  fof(f59,plain,(
% 1.69/0.59    sK3 = k2_relset_1(sK1,sK3,k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5))),
% 1.69/0.59    inference(cnf_transformation,[],[f46])).
% 1.69/0.59  fof(f617,plain,(
% 1.69/0.59    k2_relat_1(k5_relat_1(sK4,sK5)) = k2_relset_1(sK1,sK3,k5_relat_1(sK4,sK5))),
% 1.69/0.59    inference(resolution,[],[f543,f78])).
% 1.69/0.59  fof(f543,plain,(
% 1.69/0.59    m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 1.69/0.59    inference(forward_demodulation,[],[f542,f468])).
% 1.69/0.59  fof(f542,plain,(
% 1.69/0.59    m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 1.69/0.59    inference(subsumption_resolution,[],[f539,f56])).
% 1.69/0.59  fof(f539,plain,(
% 1.69/0.59    ~v1_funct_1(sK5) | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 1.69/0.59    inference(resolution,[],[f373,f58])).
% 1.69/0.59  fof(f373,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | m1_subset_1(k1_partfun1(sK1,sK2,X1,X2,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))) )),
% 1.69/0.59    inference(subsumption_resolution,[],[f371,f53])).
% 1.69/0.59  % (17964)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.69/0.59  fof(f371,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | m1_subset_1(k1_partfun1(sK1,sK2,X1,X2,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_1(sK4)) )),
% 1.69/0.59    inference(resolution,[],[f89,f55])).
% 1.69/0.59  fof(f89,plain,(
% 1.69/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~v1_funct_1(X4)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f41])).
% 1.69/0.59  fof(f41,plain,(
% 1.69/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.69/0.59    inference(flattening,[],[f40])).
% 1.69/0.59  fof(f40,plain,(
% 1.69/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.69/0.59    inference(ennf_transformation,[],[f14])).
% 1.69/0.59  fof(f14,axiom,(
% 1.69/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.69/0.59  fof(f111,plain,(
% 1.69/0.59    k2_relat_1(k5_relat_1(sK4,sK5)) = k9_relat_1(sK5,k2_relat_1(sK4))),
% 1.69/0.59    inference(resolution,[],[f107,f98])).
% 1.69/0.59  fof(f98,plain,(
% 1.69/0.59    v1_relat_1(sK5)),
% 1.69/0.59    inference(resolution,[],[f76,f58])).
% 1.69/0.59  fof(f107,plain,(
% 1.69/0.59    ( ! [X2] : (~v1_relat_1(X2) | k2_relat_1(k5_relat_1(sK4,X2)) = k9_relat_1(X2,k2_relat_1(sK4))) )),
% 1.69/0.59    inference(resolution,[],[f64,f97])).
% 1.69/0.59  fof(f64,plain,(
% 1.69/0.59    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) )),
% 1.69/0.59    inference(cnf_transformation,[],[f22])).
% 1.69/0.59  fof(f22,plain,(
% 1.69/0.59    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.69/0.59    inference(ennf_transformation,[],[f3])).
% 1.69/0.59  fof(f3,axiom,(
% 1.69/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 1.69/0.59  fof(f122,plain,(
% 1.69/0.59    r1_tarski(k9_relat_1(sK5,k2_relat_1(sK4)),k2_relat_1(sK5))),
% 1.69/0.59    inference(subsumption_resolution,[],[f121,f97])).
% 1.69/0.59  fof(f121,plain,(
% 1.69/0.59    r1_tarski(k9_relat_1(sK5,k2_relat_1(sK4)),k2_relat_1(sK5)) | ~v1_relat_1(sK4)),
% 1.69/0.59    inference(subsumption_resolution,[],[f118,f98])).
% 1.69/0.59  fof(f118,plain,(
% 1.69/0.59    r1_tarski(k9_relat_1(sK5,k2_relat_1(sK4)),k2_relat_1(sK5)) | ~v1_relat_1(sK5) | ~v1_relat_1(sK4)),
% 1.69/0.59    inference(superposition,[],[f63,f111])).
% 1.69/0.59  fof(f63,plain,(
% 1.69/0.59    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f21])).
% 1.69/0.59  fof(f21,plain,(
% 1.69/0.59    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.69/0.59    inference(ennf_transformation,[],[f4])).
% 1.69/0.59  fof(f4,axiom,(
% 1.69/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 1.69/0.59  fof(f148,plain,(
% 1.69/0.59    ~r1_tarski(sK3,k2_relat_1(sK5)) | sK3 = k2_relat_1(sK5)),
% 1.69/0.59    inference(subsumption_resolution,[],[f145,f98])).
% 1.69/0.59  fof(f145,plain,(
% 1.69/0.59    sK3 = k2_relat_1(sK5) | ~r1_tarski(sK3,k2_relat_1(sK5)) | ~v1_relat_1(sK5)),
% 1.69/0.59    inference(resolution,[],[f99,f101])).
% 1.69/0.59  fof(f101,plain,(
% 1.69/0.59    v5_relat_1(sK5,sK3)),
% 1.69/0.59    inference(resolution,[],[f79,f58])).
% 1.69/0.59  fof(f233,plain,(
% 1.69/0.59    sK2 = k9_relat_1(k2_funct_1(sK5),k2_relat_1(sK5))),
% 1.69/0.59    inference(backward_demodulation,[],[f210,f225])).
% 1.69/0.59  fof(f225,plain,(
% 1.69/0.59    sK2 = k1_relat_1(sK5)),
% 1.69/0.59    inference(backward_demodulation,[],[f140,f224])).
% 1.69/0.59  fof(f224,plain,(
% 1.69/0.59    sK2 = k1_relset_1(sK2,sK3,sK5)),
% 1.69/0.59    inference(subsumption_resolution,[],[f223,f61])).
% 1.69/0.59  fof(f61,plain,(
% 1.69/0.59    k1_xboole_0 != sK3),
% 1.69/0.59    inference(cnf_transformation,[],[f46])).
% 1.69/0.59  fof(f223,plain,(
% 1.69/0.59    k1_xboole_0 = sK3 | sK2 = k1_relset_1(sK2,sK3,sK5)),
% 1.69/0.59    inference(subsumption_resolution,[],[f221,f57])).
% 1.69/0.59  fof(f57,plain,(
% 1.69/0.59    v1_funct_2(sK5,sK2,sK3)),
% 1.69/0.59    inference(cnf_transformation,[],[f46])).
% 1.69/0.59  fof(f221,plain,(
% 1.69/0.59    ~v1_funct_2(sK5,sK2,sK3) | k1_xboole_0 = sK3 | sK2 = k1_relset_1(sK2,sK3,sK5)),
% 1.69/0.59    inference(resolution,[],[f80,f103])).
% 1.69/0.59  fof(f103,plain,(
% 1.69/0.59    sP0(sK2,sK5,sK3)),
% 1.69/0.59    inference(resolution,[],[f84,f58])).
% 1.69/0.59  fof(f84,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f52])).
% 1.69/0.59  fof(f52,plain,(
% 1.69/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.59    inference(nnf_transformation,[],[f43])).
% 1.69/0.59  fof(f43,plain,(
% 1.69/0.59    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.59    inference(definition_folding,[],[f37,f42])).
% 1.69/0.59  fof(f42,plain,(
% 1.69/0.59    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.69/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.69/0.59  fof(f37,plain,(
% 1.69/0.59    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.59    inference(flattening,[],[f36])).
% 1.69/0.59  fof(f36,plain,(
% 1.69/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.59    inference(ennf_transformation,[],[f13])).
% 1.69/0.59  fof(f13,axiom,(
% 1.69/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.69/0.59  fof(f80,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 1.69/0.59    inference(cnf_transformation,[],[f51])).
% 1.69/0.59  fof(f51,plain,(
% 1.69/0.59    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.69/0.59    inference(rectify,[],[f50])).
% 1.69/0.59  fof(f50,plain,(
% 1.69/0.59    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.69/0.59    inference(nnf_transformation,[],[f42])).
% 1.69/0.59  fof(f140,plain,(
% 1.69/0.59    k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5)),
% 1.69/0.59    inference(resolution,[],[f77,f58])).
% 1.69/0.59  fof(f77,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f33])).
% 1.69/0.59  fof(f33,plain,(
% 1.69/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.59    inference(ennf_transformation,[],[f11])).
% 1.69/0.59  fof(f11,axiom,(
% 1.69/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.69/0.59  fof(f210,plain,(
% 1.69/0.59    k1_relat_1(sK5) = k9_relat_1(k2_funct_1(sK5),k2_relat_1(sK5))),
% 1.69/0.59    inference(forward_demodulation,[],[f209,f154])).
% 1.69/0.59  fof(f154,plain,(
% 1.69/0.59    k1_relat_1(sK5) = k2_relat_1(k5_relat_1(sK5,k2_funct_1(sK5)))),
% 1.69/0.59    inference(subsumption_resolution,[],[f153,f98])).
% 1.69/0.59  fof(f153,plain,(
% 1.69/0.59    k1_relat_1(sK5) = k2_relat_1(k5_relat_1(sK5,k2_funct_1(sK5))) | ~v1_relat_1(sK5)),
% 1.69/0.59    inference(subsumption_resolution,[],[f152,f56])).
% 1.69/0.59  fof(f152,plain,(
% 1.69/0.59    k1_relat_1(sK5) = k2_relat_1(k5_relat_1(sK5,k2_funct_1(sK5))) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)),
% 1.69/0.59    inference(resolution,[],[f68,f60])).
% 1.69/0.59  fof(f60,plain,(
% 1.69/0.59    v2_funct_1(sK5)),
% 1.69/0.59    inference(cnf_transformation,[],[f46])).
% 1.69/0.59  fof(f68,plain,(
% 1.69/0.59    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f26])).
% 1.69/0.59  fof(f26,plain,(
% 1.69/0.59    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.69/0.59    inference(flattening,[],[f25])).
% 1.69/0.59  fof(f25,plain,(
% 1.69/0.59    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.69/0.59    inference(ennf_transformation,[],[f8])).
% 1.69/0.59  fof(f8,axiom,(
% 1.69/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0))))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).
% 1.69/0.59  fof(f209,plain,(
% 1.69/0.59    k2_relat_1(k5_relat_1(sK5,k2_funct_1(sK5))) = k9_relat_1(k2_funct_1(sK5),k2_relat_1(sK5))),
% 1.69/0.59    inference(subsumption_resolution,[],[f206,f98])).
% 1.69/0.59  fof(f206,plain,(
% 1.69/0.59    k2_relat_1(k5_relat_1(sK5,k2_funct_1(sK5))) = k9_relat_1(k2_funct_1(sK5),k2_relat_1(sK5)) | ~v1_relat_1(sK5)),
% 1.69/0.59    inference(resolution,[],[f124,f56])).
% 1.69/0.59  fof(f124,plain,(
% 1.69/0.59    ( ! [X0] : (~v1_funct_1(X0) | k2_relat_1(k5_relat_1(sK5,k2_funct_1(X0))) = k9_relat_1(k2_funct_1(X0),k2_relat_1(sK5)) | ~v1_relat_1(X0)) )),
% 1.69/0.59    inference(resolution,[],[f108,f65])).
% 1.69/0.59  fof(f65,plain,(
% 1.69/0.59    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f24])).
% 1.69/0.59  fof(f24,plain,(
% 1.69/0.59    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.69/0.59    inference(flattening,[],[f23])).
% 1.69/0.59  fof(f23,plain,(
% 1.69/0.59    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.69/0.59    inference(ennf_transformation,[],[f5])).
% 1.69/0.59  fof(f5,axiom,(
% 1.69/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.69/0.59  fof(f108,plain,(
% 1.69/0.59    ( ! [X3] : (~v1_relat_1(X3) | k2_relat_1(k5_relat_1(sK5,X3)) = k9_relat_1(X3,k2_relat_1(sK5))) )),
% 1.69/0.59    inference(resolution,[],[f64,f98])).
% 1.69/0.59  fof(f760,plain,(
% 1.69/0.59    r1_tarski(k9_relat_1(k2_funct_1(sK5),sK3),k2_relat_1(sK4))),
% 1.69/0.59    inference(superposition,[],[f173,f634])).
% 1.69/0.59  fof(f173,plain,(
% 1.69/0.59    ( ! [X0] : (r1_tarski(k9_relat_1(k2_funct_1(sK5),k9_relat_1(sK5,X0)),X0)) )),
% 1.69/0.59    inference(subsumption_resolution,[],[f172,f98])).
% 1.69/0.59  fof(f172,plain,(
% 1.69/0.59    ( ! [X0] : (r1_tarski(k9_relat_1(k2_funct_1(sK5),k9_relat_1(sK5,X0)),X0) | ~v1_relat_1(sK5)) )),
% 1.69/0.59    inference(subsumption_resolution,[],[f171,f56])).
% 1.69/0.59  fof(f171,plain,(
% 1.69/0.59    ( ! [X0] : (r1_tarski(k9_relat_1(k2_funct_1(sK5),k9_relat_1(sK5,X0)),X0) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)) )),
% 1.69/0.59    inference(resolution,[],[f170,f65])).
% 1.69/0.59  fof(f170,plain,(
% 1.69/0.59    ( ! [X0] : (~v1_relat_1(k2_funct_1(sK5)) | r1_tarski(k9_relat_1(k2_funct_1(sK5),k9_relat_1(sK5,X0)),X0)) )),
% 1.69/0.59    inference(subsumption_resolution,[],[f169,f98])).
% 1.69/0.59  fof(f169,plain,(
% 1.69/0.59    ( ! [X0] : (r1_tarski(k9_relat_1(k2_funct_1(sK5),k9_relat_1(sK5,X0)),X0) | ~v1_relat_1(k2_funct_1(sK5)) | ~v1_relat_1(sK5)) )),
% 1.69/0.59    inference(subsumption_resolution,[],[f168,f56])).
% 1.69/0.59  fof(f168,plain,(
% 1.69/0.59    ( ! [X0] : (r1_tarski(k9_relat_1(k2_funct_1(sK5),k9_relat_1(sK5,X0)),X0) | ~v1_relat_1(k2_funct_1(sK5)) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)) )),
% 1.69/0.59    inference(resolution,[],[f167,f66])).
% 1.69/0.59  fof(f66,plain,(
% 1.69/0.59    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f24])).
% 1.69/0.59  fof(f167,plain,(
% 1.69/0.59    ( ! [X0] : (~v1_funct_1(k2_funct_1(sK5)) | r1_tarski(k9_relat_1(k2_funct_1(sK5),k9_relat_1(sK5,X0)),X0) | ~v1_relat_1(k2_funct_1(sK5))) )),
% 1.69/0.59    inference(superposition,[],[f71,f166])).
% 1.69/0.59  fof(f166,plain,(
% 1.69/0.59    ( ! [X0] : (k9_relat_1(sK5,X0) = k10_relat_1(k2_funct_1(sK5),X0)) )),
% 1.69/0.59    inference(subsumption_resolution,[],[f165,f98])).
% 1.69/0.59  fof(f165,plain,(
% 1.69/0.59    ( ! [X0] : (k9_relat_1(sK5,X0) = k10_relat_1(k2_funct_1(sK5),X0) | ~v1_relat_1(sK5)) )),
% 1.69/0.59    inference(subsumption_resolution,[],[f164,f56])).
% 1.69/0.59  fof(f164,plain,(
% 1.69/0.59    ( ! [X0] : (k9_relat_1(sK5,X0) = k10_relat_1(k2_funct_1(sK5),X0) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)) )),
% 1.69/0.59    inference(resolution,[],[f72,f60])).
% 1.69/0.59  fof(f72,plain,(
% 1.69/0.59    ( ! [X0,X1] : (~v2_funct_1(X1) | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f31])).
% 1.69/0.59  fof(f31,plain,(
% 1.69/0.59    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.69/0.59    inference(flattening,[],[f30])).
% 1.69/0.59  fof(f30,plain,(
% 1.69/0.59    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.69/0.59    inference(ennf_transformation,[],[f7])).
% 1.69/0.59  fof(f7,axiom,(
% 1.69/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
% 1.69/0.59  fof(f71,plain,(
% 1.69/0.59    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f29])).
% 1.69/0.59  fof(f29,plain,(
% 1.69/0.59    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.69/0.59    inference(flattening,[],[f28])).
% 1.69/0.59  fof(f28,plain,(
% 1.69/0.59    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.69/0.59    inference(ennf_transformation,[],[f6])).
% 1.69/0.59  fof(f6,axiom,(
% 1.69/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 1.69/0.59  % SZS output end Proof for theBenchmark
% 1.69/0.59  % (17960)------------------------------
% 1.69/0.59  % (17960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.59  % (17960)Termination reason: Refutation
% 1.69/0.59  
% 1.69/0.59  % (17960)Memory used [KB]: 7036
% 1.69/0.59  % (17960)Time elapsed: 0.166 s
% 1.69/0.59  % (17960)------------------------------
% 1.69/0.59  % (17960)------------------------------
% 1.69/0.59  % (17956)Success in time 0.237 s
%------------------------------------------------------------------------------
