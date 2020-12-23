%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:29 EST 2020

% Result     : Theorem 4.09s
% Output     : Refutation 4.41s
% Verified   : 
% Statistics : Number of formulae       :  211 (4552 expanded)
%              Number of leaves         :   27 (1317 expanded)
%              Depth                    :   45
%              Number of atoms          : 1033 (31947 expanded)
%              Number of equality atoms :  177 (1515 expanded)
%              Maximal formula depth    :   21 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1289,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1254,f1157])).

fof(f1157,plain,(
    ! [X0] : r2_relset_1(k1_xboole_0,X0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f204,f1145])).

fof(f1145,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f1090,f298])).

fof(f298,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f297,f76])).

fof(f76,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f297,plain,(
    ! [X2] :
      ( ~ v1_funct_1(k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
      | k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f296,f76])).

fof(f296,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
      | k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f289])).

fof(f289,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
      | ~ v1_funct_1(k1_xboole_0)
      | k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[],[f229,f210])).

fof(f210,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k5_relat_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f209,f76])).

fof(f209,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ m1_subset_1(k5_relat_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(resolution,[],[f204,f112])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f229,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f228])).

fof(f228,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f116,f114])).

fof(f114,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
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
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f116,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f1090,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f1037,f118])).

fof(f118,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f75,f77])).

fof(f77,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f75,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f1037,plain,(
    v1_funct_1(k6_partfun1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f810,f968])).

fof(f968,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f965,f71])).

fof(f71,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ~ r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2))
    & v2_funct_1(sK3)
    & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK4,sK2,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK3,sK2,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f56,f55])).

fof(f55,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
            & v2_funct_1(X1)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK2,sK2,X2,k6_partfun1(sK2))
          & v2_funct_1(sK3)
          & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X2,sK3),sK3)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
          & v1_funct_2(X2,sK2,sK2)
          & v1_funct_1(X2) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v1_funct_2(sK3,sK2,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK2,sK2,X2,k6_partfun1(sK2))
        & v2_funct_1(sK3)
        & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X2,sK3),sK3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
        & v1_funct_2(X2,sK2,sK2)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2))
      & v2_funct_1(sK3)
      & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v1_funct_2(sK4,sK2,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( ( v2_funct_1(X1)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
             => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
           => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_funct_2)).

fof(f965,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(resolution,[],[f886,f124])).

fof(f124,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f886,plain,
    ( ~ r2_relset_1(sK2,sK2,sK4,sK4)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f74,f876])).

fof(f876,plain,
    ( k6_partfun1(sK2) = sK4
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f873,f68])).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f57])).

fof(f873,plain,
    ( k1_xboole_0 = sK2
    | k6_partfun1(sK2) = sK4
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(resolution,[],[f865,f196])).

fof(f196,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f195,f79])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(duplicate_literal_removal,[],[f192])).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(superposition,[],[f94,f117])).

fof(f117,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).

fof(f865,plain,
    ( ~ r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3)
    | k1_xboole_0 = sK2
    | k6_partfun1(sK2) = sK4 ),
    inference(subsumption_resolution,[],[f864,f810])).

fof(f864,plain,
    ( k1_xboole_0 = sK2
    | ~ r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3)
    | ~ v1_funct_1(k6_partfun1(sK2))
    | k6_partfun1(sK2) = sK4 ),
    inference(subsumption_resolution,[],[f858,f79])).

fof(f858,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3)
    | ~ v1_funct_1(k6_partfun1(sK2))
    | k6_partfun1(sK2) = sK4 ),
    inference(resolution,[],[f855,f646])).

fof(f646,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,sK2,sK2)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3)
      | ~ v1_funct_1(X0)
      | sK4 = X0 ) ),
    inference(subsumption_resolution,[],[f645,f66])).

fof(f66,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f645,plain,(
    ! [X0] :
      ( ~ r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X0,sK2,sK2)
      | ~ v1_funct_1(X0)
      | sK4 = X0
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f640,f68])).

fof(f640,plain,(
    ! [X0] :
      ( ~ r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X0,sK2,sK2)
      | ~ v1_funct_1(X0)
      | sK4 = X0
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_1(sK3) ) ),
    inference(duplicate_literal_removal,[],[f639])).

fof(f639,plain,(
    ! [X0] :
      ( ~ r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X0,sK2,sK2)
      | ~ v1_funct_1(X0)
      | sK4 = X0
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_1(X0) ) ),
    inference(superposition,[],[f628,f114])).

fof(f628,plain,(
    ! [X4] :
      ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X4,sK3),sK3)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X4,sK2,sK2)
      | ~ v1_funct_1(X4)
      | sK4 = X4 ) ),
    inference(forward_demodulation,[],[f627,f233])).

fof(f233,plain,(
    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f232,f69])).

fof(f69,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f232,plain,
    ( ~ v1_funct_1(sK4)
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f231,f71])).

fof(f231,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4)
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f230,f66])).

fof(f230,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4)
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f226,f68])).

fof(f226,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4)
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(resolution,[],[f116,f187])).

fof(f187,plain,
    ( ~ m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f180,f68])).

fof(f180,plain,
    ( sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(resolution,[],[f112,f72])).

fof(f72,plain,(
    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f627,plain,(
    ! [X4] :
      ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X4,sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3))
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X4,sK2,sK2)
      | ~ v1_funct_1(X4)
      | sK4 = X4 ) ),
    inference(subsumption_resolution,[],[f626,f69])).

fof(f626,plain,(
    ! [X4] :
      ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X4,sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3))
      | k1_xboole_0 = sK2
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X4,sK2,sK2)
      | ~ v1_funct_1(X4)
      | sK4 = X4 ) ),
    inference(subsumption_resolution,[],[f619,f71])).

fof(f619,plain,(
    ! [X4] :
      ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X4,sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | k1_xboole_0 = sK2
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X4,sK2,sK2)
      | ~ v1_funct_1(X4)
      | sK4 = X4 ) ),
    inference(resolution,[],[f611,f70])).

fof(f70,plain,(
    v1_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f611,plain,(
    ! [X8,X7,X9] :
      ( ~ v1_funct_2(X9,X7,sK2)
      | ~ r2_relset_1(X7,sK2,k1_partfun1(X7,sK2,sK2,sK2,X8,sK3),k1_partfun1(X7,sK2,sK2,sK2,X9,sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,sK2)))
      | k1_xboole_0 = sK2
      | ~ v1_funct_1(X9)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK2)))
      | ~ v1_funct_2(X8,X7,sK2)
      | ~ v1_funct_1(X8)
      | X8 = X9 ) ),
    inference(subsumption_resolution,[],[f610,f67])).

fof(f67,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f610,plain,(
    ! [X8,X7,X9] :
      ( k1_xboole_0 = sK2
      | ~ r2_relset_1(X7,sK2,k1_partfun1(X7,sK2,sK2,sK2,X8,sK3),k1_partfun1(X7,sK2,sK2,sK2,X9,sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,sK2)))
      | ~ v1_funct_2(X9,X7,sK2)
      | ~ v1_funct_1(X9)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK2)))
      | ~ v1_funct_2(X8,X7,sK2)
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(sK3,sK2,sK2)
      | X8 = X9 ) ),
    inference(duplicate_literal_removal,[],[f604])).

fof(f604,plain,(
    ! [X8,X7,X9] :
      ( k1_xboole_0 = sK2
      | k1_xboole_0 = sK2
      | ~ r2_relset_1(X7,sK2,k1_partfun1(X7,sK2,sK2,sK2,X8,sK3),k1_partfun1(X7,sK2,sK2,sK2,X9,sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,sK2)))
      | ~ v1_funct_2(X9,X7,sK2)
      | ~ v1_funct_1(X9)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK2)))
      | ~ v1_funct_2(X8,X7,sK2)
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(sK3,sK2,sK2)
      | X8 = X9 ) ),
    inference(resolution,[],[f518,f68])).

fof(f518,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | k1_xboole_0 = X5
      | k1_xboole_0 = X6
      | ~ r2_relset_1(X7,X6,k1_partfun1(X7,X5,X5,X6,X8,sK3),k1_partfun1(X7,X5,X5,X6,X9,sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X5)))
      | ~ v1_funct_2(X9,X7,X5)
      | ~ v1_funct_1(X9)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,X5)))
      | ~ v1_funct_2(X8,X7,X5)
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(sK3,X5,X6)
      | X8 = X9 ) ),
    inference(duplicate_literal_removal,[],[f517])).

fof(f517,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ v1_funct_2(sK3,X5,X6)
      | k1_xboole_0 = X5
      | k1_xboole_0 = X6
      | ~ r2_relset_1(X7,X6,k1_partfun1(X7,X5,X5,X6,X8,sK3),k1_partfun1(X7,X5,X5,X6,X9,sK3))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X5)))
      | ~ v1_funct_2(X9,X7,X5)
      | ~ v1_funct_1(X9)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,X5)))
      | ~ v1_funct_2(X8,X7,X5)
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | X8 = X9
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X5)))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,X5))) ) ),
    inference(resolution,[],[f395,f112])).

fof(f395,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_relset_1(X2,X0,X3,X4)
      | ~ v1_funct_2(sK3,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | ~ r2_relset_1(X2,X1,k1_partfun1(X2,X0,X0,X1,X3,sK3),k1_partfun1(X2,X0,X0,X1,X4,sK3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_2(X4,X2,X0)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_2(X3,X2,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f393,f66])).

fof(f393,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK3,X0,X1)
      | ~ v1_funct_1(sK3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | ~ r2_relset_1(X2,X1,k1_partfun1(X2,X0,X0,X1,X3,sK3),k1_partfun1(X2,X0,X0,X1,X4,sK3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_2(X4,X2,X0)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_2(X3,X2,X0)
      | ~ v1_funct_1(X3)
      | r2_relset_1(X2,X0,X3,X4) ) ),
    inference(resolution,[],[f288,f73])).

fof(f73,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f288,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_funct_2(X1,X0,X2)
      | ~ v1_funct_1(X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ r2_relset_1(X3,X2,k1_partfun1(X3,X0,X0,X2,X4,X1),k1_partfun1(X3,X0,X0,X2,X5,X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | ~ v1_funct_2(X5,X3,X0)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | ~ v1_funct_2(X4,X3,X0)
      | ~ v1_funct_1(X4)
      | r2_relset_1(X3,X0,X4,X5) ) ),
    inference(resolution,[],[f191,f101])).

fof(f101,plain,(
    ! [X6,X2,X0,X8,X7,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0)))
      | ~ v1_funct_2(X8,X6,X0)
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0)))
      | ~ v1_funct_2(X7,X6,X0)
      | ~ v1_funct_1(X7)
      | r2_relset_1(X6,X0,X7,X8) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),sK7(X0,X1,X2))
          & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK7(X0,X1,X2),X1))
          & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0)))
          & v1_funct_2(sK7(X0,X1,X2),sK5(X0,X1,X2),X0)
          & v1_funct_1(sK7(X0,X1,X2))
          & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0)))
          & v1_funct_2(sK6(X0,X1,X2),sK5(X0,X1,X2),X0)
          & v1_funct_1(sK6(X0,X1,X2)) ) )
      & ( ! [X6,X7] :
            ( ! [X8] :
                ( r2_relset_1(X6,X0,X7,X8)
                | ~ r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1))
                | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0)))
                | ~ v1_funct_2(X8,X6,X0)
                | ~ v1_funct_1(X8) )
            | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0)))
            | ~ v1_funct_2(X7,X6,X0)
            | ~ v1_funct_1(X7) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f61,f63,f62])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ? [X5] :
              ( ~ r2_relset_1(X3,X0,X4,X5)
              & r2_relset_1(X3,X2,k1_partfun1(X3,X0,X0,X2,X4,X1),k1_partfun1(X3,X0,X0,X2,X5,X1))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
              & v1_funct_2(X5,X3,X0)
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
          & v1_funct_2(X4,X3,X0)
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ~ r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),X5)
            & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,X5,X1))
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0)))
            & v1_funct_2(X5,sK5(X0,X1,X2),X0)
            & v1_funct_1(X5) )
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0)))
        & v1_funct_2(sK6(X0,X1,X2),sK5(X0,X1,X2),X0)
        & v1_funct_1(sK6(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ~ r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),X5)
          & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,X5,X1))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0)))
          & v1_funct_2(X5,sK5(X0,X1,X2),X0)
          & v1_funct_1(X5) )
     => ( ~ r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),sK7(X0,X1,X2))
        & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK7(X0,X1,X2),X1))
        & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0)))
        & v1_funct_2(sK7(X0,X1,X2),sK5(X0,X1,X2),X0)
        & v1_funct_1(sK7(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3,X4] :
            ( ? [X5] :
                ( ~ r2_relset_1(X3,X0,X4,X5)
                & r2_relset_1(X3,X2,k1_partfun1(X3,X0,X0,X2,X4,X1),k1_partfun1(X3,X0,X0,X2,X5,X1))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
                & v1_funct_2(X5,X3,X0)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
            & v1_funct_2(X4,X3,X0)
            & v1_funct_1(X4) ) )
      & ( ! [X6,X7] :
            ( ! [X8] :
                ( r2_relset_1(X6,X0,X7,X8)
                | ~ r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1))
                | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0)))
                | ~ v1_funct_2(X8,X6,X0)
                | ~ v1_funct_1(X8) )
            | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0)))
            | ~ v1_funct_2(X7,X6,X0)
            | ~ v1_funct_1(X7) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0,X2,X1] :
      ( ( sP0(X0,X2,X1)
        | ? [X3,X4] :
            ( ? [X5] :
                ( ~ r2_relset_1(X3,X0,X4,X5)
                & r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
                & v1_funct_2(X5,X3,X0)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
            & v1_funct_2(X4,X3,X0)
            & v1_funct_1(X4) ) )
      & ( ! [X3,X4] :
            ( ! [X5] :
                ( r2_relset_1(X3,X0,X4,X5)
                | ~ r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
                | ~ v1_funct_2(X5,X3,X0)
                | ~ v1_funct_1(X5) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
            | ~ v1_funct_2(X4,X3,X0)
            | ~ v1_funct_1(X4) )
        | ~ sP0(X0,X2,X1) ) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X2,X1] :
      ( sP0(X0,X2,X1)
    <=> ! [X3,X4] :
          ( ! [X5] :
              ( r2_relset_1(X3,X0,X4,X5)
              | ~ r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))
              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
              | ~ v1_funct_2(X5,X3,X0)
              | ~ v1_funct_1(X5) )
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
          | ~ v1_funct_2(X4,X3,X0)
          | ~ v1_funct_1(X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f191,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f110,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ v2_funct_1(X1)
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( ( v2_funct_1(X1)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ v2_funct_1(X1) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X1,X2,X0] :
      ( ( ( v2_funct_1(X2)
          | ~ sP0(X0,X2,X1) )
        & ( sP0(X0,X2,X1)
          | ~ v2_funct_1(X2) ) )
      | ~ sP1(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X1,X2,X0] :
      ( ( v2_funct_1(X2)
      <=> sP0(X0,X2,X1) )
      | ~ sP1(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X2,X0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X2,X0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f41,f53,f52])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
      <=> ! [X3,X4] :
            ( ! [X5] :
                ( r2_relset_1(X3,X0,X4,X5)
                | ~ r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
                | ~ v1_funct_2(X5,X3,X0)
                | ~ v1_funct_1(X5) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
            | ~ v1_funct_2(X4,X3,X0)
            | ~ v1_funct_1(X4) ) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
      <=> ! [X3,X4] :
            ( ! [X5] :
                ( r2_relset_1(X3,X0,X4,X5)
                | ~ r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
                | ~ v1_funct_2(X5,X3,X0)
                | ~ v1_funct_1(X5) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
            | ~ v1_funct_2(X4,X3,X0)
            | ~ v1_funct_1(X4) ) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ~ ( ~ ( v2_funct_1(X2)
            <=> ! [X3,X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
                    & v1_funct_2(X4,X3,X0)
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
                        & v1_funct_2(X5,X3,X0)
                        & v1_funct_1(X5) )
                     => ( r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))
                       => r2_relset_1(X3,X0,X4,X5) ) ) ) )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_2)).

fof(f855,plain,(
    v1_funct_2(k6_partfun1(sK2),sK2,sK2) ),
    inference(resolution,[],[f816,f79])).

fof(f816,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(k6_partfun1(sK2),sK2,sK2) ) ),
    inference(resolution,[],[f810,f151])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(k6_partfun1(X0))
      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_funct_2(k6_partfun1(X0),X0,X0) ) ),
    inference(forward_demodulation,[],[f147,f119])).

fof(f119,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f81,f77])).

fof(f81,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k6_partfun1(X0),X0,k2_relat_1(k6_partfun1(X0)))
      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(k6_partfun1(X0)) ) ),
    inference(superposition,[],[f145,f120])).

fof(f120,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f80,f77])).

fof(f80,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f134,f90])).

fof(f90,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f134,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X3)
      | v1_funct_2(X2,k1_relat_1(X2),k2_relat_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f86,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f74,plain,(
    ~ r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f57])).

fof(f810,plain,(
    v1_funct_1(k6_partfun1(sK2)) ),
    inference(resolution,[],[f803,f68])).

fof(f803,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_funct_1(k6_partfun1(sK2)) ) ),
    inference(resolution,[],[f796,f68])).

fof(f796,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | v1_funct_1(k6_partfun1(sK2)) ) ),
    inference(resolution,[],[f788,f68])).

fof(f788,plain,(
    ! [X14,X12,X10,X15,X13,X11] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | v1_funct_1(k6_partfun1(sK2)) ) ),
    inference(resolution,[],[f786,f68])).

fof(f786,plain,(
    ! [X57,X54,X52,X58,X56,X55,X53,X51] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))
      | v1_funct_1(k6_partfun1(sK2)) ) ),
    inference(subsumption_resolution,[],[f781,f179])).

fof(f179,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK3,sK2,k2_relat_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f177,f66])).

fof(f177,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK3,sK2,k2_relat_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(superposition,[],[f145,f174])).

fof(f174,plain,(
    sK2 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f173,f66])).

fof(f173,plain,
    ( sK2 = k1_relat_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f170,f68])).

fof(f170,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | sK2 = k1_relat_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f162,f67])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relat_1(X1) = X0
      | ~ v1_funct_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(superposition,[],[f91,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f91,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(f781,plain,(
    ! [X57,X54,X52,X58,X56,X55,X53,X51] :
      ( v1_funct_1(k6_partfun1(sK2))
      | ~ v1_funct_2(sK3,sK2,k2_relat_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X57,X58))) ) ),
    inference(resolution,[],[f773,f268])).

fof(f268,plain,(
    ! [X14,X13] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3))))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) ) ),
    inference(forward_demodulation,[],[f264,f174])).

fof(f264,plain,(
    ! [X14,X13] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) ) ),
    inference(resolution,[],[f167,f66])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(resolution,[],[f136,f90])).

fof(f136,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X3)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f87,f84])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f773,plain,(
    ! [X47,X52,X50,X48,X46,X51,X49] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X46,k2_relat_1(sK3))))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ v1_funct_2(sK3,X46,k2_relat_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) ) ),
    inference(subsumption_resolution,[],[f768,f179])).

fof(f768,plain,(
    ! [X47,X52,X50,X48,X46,X51,X49] :
      ( ~ v1_funct_2(sK3,sK2,k2_relat_1(sK3))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X46,k2_relat_1(sK3))))
      | ~ v1_funct_2(sK3,X46,k2_relat_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) ) ),
    inference(resolution,[],[f760,f268])).

fof(f760,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
      | ~ v1_funct_2(sK3,X0,k2_relat_1(sK3))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(sK3))))
      | ~ v1_funct_2(sK3,X1,k2_relat_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(equality_resolution,[],[f759])).

fof(f759,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_relat_1(sK3) != X1
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK3,X0,X1)
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(sK3))))
      | ~ v1_funct_2(sK3,X2,k2_relat_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ) ),
    inference(equality_resolution,[],[f753])).

fof(f753,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k2_relat_1(sK3) != X1
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(sK3,X2,X3)
      | k2_relat_1(sK3) != X3
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK3,X0,X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(duplicate_literal_removal,[],[f752])).

fof(f752,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k2_relat_1(sK3) != X1
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(sK3,X2,X3)
      | k2_relat_1(sK3) != X3
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK3,X0,X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f747,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f747,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k2_relset_1(X2,X3,sK3) != X3
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK3,X0,X1)
      | k2_relat_1(sK3) != X1
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(sK3,X2,X3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(duplicate_literal_removal,[],[f746])).

fof(f746,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k2_relat_1(sK3) != X1
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK3,X0,X1)
      | k2_relset_1(X2,X3,sK3) != X3
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(sK3,X2,X3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f744,f93])).

fof(f744,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k2_relset_1(X0,X1,sK3) != X1
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK3,X0,X1)
      | k2_relset_1(X2,X3,sK3) != X3
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(sK3,X2,X3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(resolution,[],[f719,f90])).

fof(f719,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X6)
      | v1_funct_1(k6_partfun1(sK2))
      | k2_relset_1(X2,X3,sK3) != X3
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(sK3,X2,X3)
      | k2_relset_1(X4,X5,sK3) != X5
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_2(sK3,X4,X5)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X6))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f690,f84])).

fof(f690,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_relat_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k6_partfun1(sK2))
      | k2_relset_1(X2,X3,sK3) != X3
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(sK3,X2,X3)
      | k2_relset_1(X4,X5,sK3) != X5
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_2(sK3,X4,X5) ) ),
    inference(forward_demodulation,[],[f689,f174])).

fof(f689,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k6_partfun1(k1_relat_1(sK3)))
      | ~ v1_relat_1(sK3)
      | k2_relset_1(X2,X3,sK3) != X3
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(sK3,X2,X3)
      | k2_relset_1(X4,X5,sK3) != X5
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_2(sK3,X4,X5) ) ),
    inference(subsumption_resolution,[],[f687,f66])).

fof(f687,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK3)
      | v1_funct_1(k6_partfun1(k1_relat_1(sK3)))
      | ~ v1_relat_1(sK3)
      | k2_relset_1(X2,X3,sK3) != X3
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(sK3,X2,X3)
      | k2_relset_1(X4,X5,sK3) != X5
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_2(sK3,X4,X5) ) ),
    inference(resolution,[],[f499,f73])).

fof(f499,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ v2_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | v1_funct_1(k6_partfun1(k1_relat_1(X0)))
      | ~ v1_relat_1(X0)
      | k2_relset_1(X3,X4,X0) != X4
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X0,X3,X4)
      | k2_relset_1(X5,X6,X0) != X6
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_2(X0,X5,X6) ) ),
    inference(duplicate_literal_removal,[],[f496])).

fof(f496,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k6_partfun1(k1_relat_1(X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relset_1(X3,X4,X0) != X4
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X0,X3,X4)
      | k2_relset_1(X5,X6,X0) != X6
      | ~ v2_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_2(X0,X5,X6)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f360,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f360,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_funct_1(k6_partfun1(k1_relat_1(X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relset_1(X5,X6,X0) != X6
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_2(X0,X5,X6) ) ),
    inference(duplicate_literal_removal,[],[f359])).

fof(f359,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_funct_1(k6_partfun1(k1_relat_1(X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relset_1(X5,X6,X0) != X6
      | ~ v2_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_2(X0,X5,X6)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f280,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f280,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ v1_funct_1(k2_funct_1(X5))
      | ~ m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_funct_1(k6_partfun1(k1_relat_1(X5)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_1(X5)
      | ~ v2_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(duplicate_literal_removal,[],[f278])).

fof(f278,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( v1_funct_1(k6_partfun1(k1_relat_1(X5)))
      | ~ m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_1(k2_funct_1(X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_1(X5)
      | ~ v2_funct_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(superposition,[],[f216,f122])).

fof(f122,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f88,f77])).

fof(f88,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f216,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k5_relat_1(X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f215])).

fof(f215,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k5_relat_1(X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f115,f114])).

fof(f115,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f204,plain,(
    ! [X0] : r2_relset_1(k1_xboole_0,X0,k5_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f199,f76])).

fof(f199,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | r2_relset_1(k1_xboole_0,X0,k5_relat_1(k1_xboole_0,X1),X1) ) ),
    inference(superposition,[],[f196,f118])).

fof(f1254,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1062,f1234])).

fof(f1234,plain,(
    k1_xboole_0 = sK4 ),
    inference(resolution,[],[f1060,f972])).

fof(f972,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f71,f968])).

fof(f1060,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = sK4 ) ),
    inference(trivial_inequality_removal,[],[f978])).

fof(f978,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = sK4 ) ),
    inference(backward_demodulation,[],[f189,f968])).

fof(f189,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != sK2
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = sK4 ) ),
    inference(superposition,[],[f137,f176])).

fof(f176,plain,(
    sK2 = k1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f175,f69])).

fof(f175,plain,
    ( sK2 = k1_relat_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f171,f71])).

fof(f171,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | sK2 = k1_relat_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f162,f70])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f130,f90])).

fof(f130,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X3)
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | k1_xboole_0 != k1_relat_1(X2) ) ),
    inference(resolution,[],[f82,f84])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f1062,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k1_xboole_0) ),
    inference(forward_demodulation,[],[f973,f118])).

fof(f973,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k6_partfun1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f74,f968])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:02:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (23623)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (23624)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (23640)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (23632)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.55  % (23635)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (23627)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (23639)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.56  % (23631)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.56  % (23643)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.57  % (23621)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.58  % (23637)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.59  % (23629)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.58/0.60  % (23619)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.58/0.60  % (23617)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.58/0.61  % (23634)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.58/0.61  % (23636)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.58/0.61  % (23644)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.90/0.62  % (23642)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.90/0.62  % (23628)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.90/0.62  % (23641)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.90/0.62  % (23645)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.90/0.62  % (23620)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.90/0.62  % (23626)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.90/0.63  % (23627)Refutation not found, incomplete strategy% (23627)------------------------------
% 1.90/0.63  % (23627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.63  % (23633)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.90/0.64  % (23633)Refutation not found, incomplete strategy% (23633)------------------------------
% 1.90/0.64  % (23633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.64  % (23633)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.64  
% 1.90/0.64  % (23633)Memory used [KB]: 10746
% 1.90/0.64  % (23633)Time elapsed: 0.205 s
% 1.90/0.64  % (23633)------------------------------
% 1.90/0.64  % (23633)------------------------------
% 1.90/0.65  % (23618)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.90/0.65  % (23627)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.65  
% 1.90/0.65  % (23627)Memory used [KB]: 11641
% 1.90/0.65  % (23627)Time elapsed: 0.199 s
% 1.90/0.65  % (23627)------------------------------
% 1.90/0.65  % (23627)------------------------------
% 1.90/0.65  % (23622)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.90/0.66  % (23625)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 2.22/0.67  % (23646)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 2.22/0.67  % (23638)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 2.22/0.69  % (23630)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 3.54/0.84  % (23641)Time limit reached!
% 3.54/0.84  % (23641)------------------------------
% 3.54/0.84  % (23641)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.54/0.84  % (23641)Termination reason: Time limit
% 3.54/0.84  
% 3.54/0.84  % (23641)Memory used [KB]: 12153
% 3.54/0.84  % (23641)Time elapsed: 0.410 s
% 3.54/0.84  % (23641)------------------------------
% 3.54/0.84  % (23641)------------------------------
% 3.54/0.85  % (23647)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.66/0.87  % (23619)Time limit reached!
% 3.66/0.87  % (23619)------------------------------
% 3.66/0.87  % (23619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.66/0.87  % (23619)Termination reason: Time limit
% 3.66/0.87  
% 3.66/0.87  % (23619)Memory used [KB]: 6268
% 3.66/0.87  % (23619)Time elapsed: 0.434 s
% 3.66/0.87  % (23619)------------------------------
% 3.66/0.87  % (23619)------------------------------
% 3.66/0.90  % (23648)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 4.09/0.93  % (23631)Time limit reached!
% 4.09/0.93  % (23631)------------------------------
% 4.09/0.93  % (23631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.09/0.93  % (23646)Time limit reached!
% 4.09/0.93  % (23646)------------------------------
% 4.09/0.93  % (23646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.09/0.93  % (23646)Termination reason: Time limit
% 4.09/0.93  % (23646)Termination phase: Saturation
% 4.09/0.93  
% 4.09/0.93  % (23646)Memory used [KB]: 3582
% 4.09/0.93  % (23646)Time elapsed: 0.500 s
% 4.09/0.93  % (23646)------------------------------
% 4.09/0.93  % (23646)------------------------------
% 4.09/0.93  % (23645)Refutation not found, incomplete strategy% (23645)------------------------------
% 4.09/0.93  % (23645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.09/0.93  % (23645)Termination reason: Refutation not found, incomplete strategy
% 4.09/0.93  
% 4.09/0.93  % (23645)Memory used [KB]: 12025
% 4.09/0.93  % (23645)Time elapsed: 0.512 s
% 4.09/0.93  % (23645)------------------------------
% 4.09/0.93  % (23645)------------------------------
% 4.09/0.95  % (23631)Termination reason: Time limit
% 4.09/0.95  % (23631)Termination phase: Saturation
% 4.09/0.95  
% 4.09/0.95  % (23631)Memory used [KB]: 5373
% 4.09/0.95  % (23631)Time elapsed: 0.500 s
% 4.09/0.95  % (23631)------------------------------
% 4.09/0.95  % (23631)------------------------------
% 4.09/0.95  % (23623)Time limit reached!
% 4.09/0.95  % (23623)------------------------------
% 4.09/0.95  % (23623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.09/0.95  % (23623)Termination reason: Time limit
% 4.09/0.95  
% 4.09/0.95  % (23623)Memory used [KB]: 14200
% 4.09/0.95  % (23623)Time elapsed: 0.522 s
% 4.09/0.95  % (23623)------------------------------
% 4.09/0.95  % (23623)------------------------------
% 4.09/0.96  % (23639)Refutation found. Thanks to Tanya!
% 4.09/0.96  % SZS status Theorem for theBenchmark
% 4.41/0.96  % SZS output start Proof for theBenchmark
% 4.41/0.96  fof(f1289,plain,(
% 4.41/0.96    $false),
% 4.41/0.96    inference(subsumption_resolution,[],[f1254,f1157])).
% 4.41/0.96  fof(f1157,plain,(
% 4.41/0.96    ( ! [X0] : (r2_relset_1(k1_xboole_0,X0,k1_xboole_0,k1_xboole_0)) )),
% 4.41/0.96    inference(backward_demodulation,[],[f204,f1145])).
% 4.41/0.96  fof(f1145,plain,(
% 4.41/0.96    k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0)),
% 4.41/0.96    inference(resolution,[],[f1090,f298])).
% 4.41/0.96  fof(f298,plain,(
% 4.41/0.96    ~v1_funct_1(k1_xboole_0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0)),
% 4.41/0.96    inference(subsumption_resolution,[],[f297,f76])).
% 4.41/0.96  fof(f76,plain,(
% 4.41/0.96    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 4.41/0.96    inference(cnf_transformation,[],[f1])).
% 4.41/0.96  fof(f1,axiom,(
% 4.41/0.96    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 4.41/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 4.41/0.96  fof(f297,plain,(
% 4.41/0.96    ( ! [X2] : (~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) | k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0)) )),
% 4.41/0.96    inference(subsumption_resolution,[],[f296,f76])).
% 4.41/0.96  fof(f296,plain,(
% 4.41/0.96    ( ! [X2,X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) | k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0)) )),
% 4.41/0.96    inference(duplicate_literal_removal,[],[f289])).
% 4.41/0.96  fof(f289,plain,(
% 4.41/0.96    ( ! [X2,X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) | ~v1_funct_1(k1_xboole_0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0)) )),
% 4.41/0.96    inference(resolution,[],[f229,f210])).
% 4.41/0.96  fof(f210,plain,(
% 4.41/0.96    ( ! [X0] : (~m1_subset_1(k5_relat_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0)) )),
% 4.41/0.96    inference(subsumption_resolution,[],[f209,f76])).
% 4.41/0.96  fof(f209,plain,(
% 4.41/0.96    ( ! [X0] : (k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | ~m1_subset_1(k5_relat_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 4.41/0.96    inference(resolution,[],[f204,f112])).
% 4.41/0.96  fof(f112,plain,(
% 4.41/0.96    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.41/0.96    inference(cnf_transformation,[],[f65])).
% 4.41/0.96  fof(f65,plain,(
% 4.41/0.96    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.41/0.96    inference(nnf_transformation,[],[f45])).
% 4.41/0.96  fof(f45,plain,(
% 4.41/0.96    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.41/0.96    inference(flattening,[],[f44])).
% 4.41/0.96  fof(f44,plain,(
% 4.41/0.96    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 4.41/0.96    inference(ennf_transformation,[],[f12])).
% 4.41/0.96  fof(f12,axiom,(
% 4.41/0.96    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 4.41/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 4.41/0.96  fof(f229,plain,(
% 4.41/0.96    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 4.41/0.96    inference(duplicate_literal_removal,[],[f228])).
% 4.41/0.96  fof(f228,plain,(
% 4.41/0.96    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 4.41/0.96    inference(superposition,[],[f116,f114])).
% 4.41/0.96  fof(f114,plain,(
% 4.41/0.96    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 4.41/0.96    inference(cnf_transformation,[],[f47])).
% 4.41/0.96  fof(f47,plain,(
% 4.41/0.96    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 4.41/0.96    inference(flattening,[],[f46])).
% 4.41/0.96  fof(f46,plain,(
% 4.41/0.96    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 4.41/0.96    inference(ennf_transformation,[],[f15])).
% 4.41/0.96  fof(f15,axiom,(
% 4.41/0.96    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 4.41/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 4.41/0.96  fof(f116,plain,(
% 4.41/0.96    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 4.41/0.96    inference(cnf_transformation,[],[f49])).
% 4.41/0.96  fof(f49,plain,(
% 4.41/0.96    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 4.41/0.96    inference(flattening,[],[f48])).
% 4.41/0.96  fof(f48,plain,(
% 4.41/0.96    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 4.41/0.96    inference(ennf_transformation,[],[f13])).
% 4.41/0.96  fof(f13,axiom,(
% 4.41/0.96    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 4.41/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 4.41/0.96  fof(f1090,plain,(
% 4.41/0.96    v1_funct_1(k1_xboole_0)),
% 4.41/0.96    inference(forward_demodulation,[],[f1037,f118])).
% 4.41/0.96  fof(f118,plain,(
% 4.41/0.96    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 4.41/0.96    inference(definition_unfolding,[],[f75,f77])).
% 4.41/0.96  fof(f77,plain,(
% 4.41/0.96    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 4.41/0.96    inference(cnf_transformation,[],[f16])).
% 4.41/0.96  fof(f16,axiom,(
% 4.41/0.96    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 4.41/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 4.41/0.96  fof(f75,plain,(
% 4.41/0.96    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 4.41/0.96    inference(cnf_transformation,[],[f7])).
% 4.41/0.96  fof(f7,axiom,(
% 4.41/0.96    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 4.41/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 4.41/0.96  fof(f1037,plain,(
% 4.41/0.96    v1_funct_1(k6_partfun1(k1_xboole_0))),
% 4.41/0.96    inference(backward_demodulation,[],[f810,f968])).
% 4.41/0.96  fof(f968,plain,(
% 4.41/0.96    k1_xboole_0 = sK2),
% 4.41/0.96    inference(subsumption_resolution,[],[f965,f71])).
% 4.41/0.96  fof(f71,plain,(
% 4.41/0.96    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 4.41/0.96    inference(cnf_transformation,[],[f57])).
% 4.41/0.96  fof(f57,plain,(
% 4.41/0.96    (~r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 4.41/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f56,f55])).
% 4.41/0.96  fof(f55,plain,(
% 4.41/0.96    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK2,sK2,X2,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X2,sK3),sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(X2,sK2,sK2) & v1_funct_1(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 4.41/0.96    introduced(choice_axiom,[])).
% 4.41/0.96  fof(f56,plain,(
% 4.41/0.96    ? [X2] : (~r2_relset_1(sK2,sK2,X2,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X2,sK3),sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(X2,sK2,sK2) & v1_funct_1(X2)) => (~r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4))),
% 4.41/0.96    introduced(choice_axiom,[])).
% 4.41/0.96  fof(f25,plain,(
% 4.41/0.96    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 4.41/0.96    inference(flattening,[],[f24])).
% 4.41/0.96  fof(f24,plain,(
% 4.41/0.96    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 4.41/0.96    inference(ennf_transformation,[],[f23])).
% 4.41/0.96  fof(f23,negated_conjecture,(
% 4.41/0.96    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 4.41/0.96    inference(negated_conjecture,[],[f22])).
% 4.41/0.96  fof(f22,conjecture,(
% 4.41/0.96    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 4.41/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_funct_2)).
% 4.41/0.96  fof(f965,plain,(
% 4.41/0.96    k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 4.41/0.96    inference(resolution,[],[f886,f124])).
% 4.41/0.96  fof(f124,plain,(
% 4.41/0.96    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.41/0.96    inference(duplicate_literal_removal,[],[f123])).
% 4.41/0.96  fof(f123,plain,(
% 4.41/0.96    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.41/0.96    inference(equality_resolution,[],[f113])).
% 4.41/0.96  fof(f113,plain,(
% 4.41/0.96    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.41/0.96    inference(cnf_transformation,[],[f65])).
% 4.41/0.96  fof(f886,plain,(
% 4.41/0.96    ~r2_relset_1(sK2,sK2,sK4,sK4) | k1_xboole_0 = sK2),
% 4.41/0.96    inference(superposition,[],[f74,f876])).
% 4.41/0.96  fof(f876,plain,(
% 4.41/0.96    k6_partfun1(sK2) = sK4 | k1_xboole_0 = sK2),
% 4.41/0.96    inference(subsumption_resolution,[],[f873,f68])).
% 4.41/0.96  fof(f68,plain,(
% 4.41/0.96    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 4.41/0.96    inference(cnf_transformation,[],[f57])).
% 4.41/0.96  fof(f873,plain,(
% 4.41/0.96    k1_xboole_0 = sK2 | k6_partfun1(sK2) = sK4 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 4.41/0.96    inference(resolution,[],[f865,f196])).
% 4.41/0.96  fof(f196,plain,(
% 4.41/0.96    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.41/0.96    inference(subsumption_resolution,[],[f195,f79])).
% 4.41/0.96  fof(f79,plain,(
% 4.41/0.96    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 4.41/0.96    inference(cnf_transformation,[],[f14])).
% 4.41/0.96  fof(f14,axiom,(
% 4.41/0.96    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 4.41/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 4.41/0.96  fof(f195,plain,(
% 4.41/0.96    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 4.41/0.96    inference(duplicate_literal_removal,[],[f192])).
% 4.41/0.96  fof(f192,plain,(
% 4.41/0.96    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 4.41/0.96    inference(superposition,[],[f94,f117])).
% 4.41/0.96  fof(f117,plain,(
% 4.41/0.96    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.41/0.96    inference(cnf_transformation,[],[f51])).
% 4.41/0.96  fof(f51,plain,(
% 4.41/0.96    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.41/0.96    inference(flattening,[],[f50])).
% 4.41/0.96  fof(f50,plain,(
% 4.41/0.96    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 4.41/0.96    inference(ennf_transformation,[],[f11])).
% 4.41/0.96  fof(f11,axiom,(
% 4.41/0.96    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 4.41/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 4.41/0.96  fof(f94,plain,(
% 4.41/0.96    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.41/0.96    inference(cnf_transformation,[],[f37])).
% 4.41/0.96  fof(f37,plain,(
% 4.41/0.96    ! [X0,X1,X2] : ((r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.41/0.96    inference(ennf_transformation,[],[f17])).
% 4.41/0.96  fof(f17,axiom,(
% 4.41/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 4.41/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).
% 4.41/0.96  fof(f865,plain,(
% 4.41/0.96    ~r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3) | k1_xboole_0 = sK2 | k6_partfun1(sK2) = sK4),
% 4.41/0.96    inference(subsumption_resolution,[],[f864,f810])).
% 4.41/0.96  fof(f864,plain,(
% 4.41/0.96    k1_xboole_0 = sK2 | ~r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3) | ~v1_funct_1(k6_partfun1(sK2)) | k6_partfun1(sK2) = sK4),
% 4.41/0.96    inference(subsumption_resolution,[],[f858,f79])).
% 4.41/0.96  fof(f858,plain,(
% 4.41/0.96    k1_xboole_0 = sK2 | ~m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~r2_relset_1(sK2,sK2,k5_relat_1(k6_partfun1(sK2),sK3),sK3) | ~v1_funct_1(k6_partfun1(sK2)) | k6_partfun1(sK2) = sK4),
% 4.41/0.96    inference(resolution,[],[f855,f646])).
% 4.41/0.96  fof(f646,plain,(
% 4.41/0.96    ( ! [X0] : (~v1_funct_2(X0,sK2,sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3) | ~v1_funct_1(X0) | sK4 = X0) )),
% 4.41/0.96    inference(subsumption_resolution,[],[f645,f66])).
% 4.41/0.96  fof(f66,plain,(
% 4.41/0.96    v1_funct_1(sK3)),
% 4.41/0.96    inference(cnf_transformation,[],[f57])).
% 4.41/0.96  fof(f645,plain,(
% 4.41/0.96    ( ! [X0] : (~r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X0,sK2,sK2) | ~v1_funct_1(X0) | sK4 = X0 | ~v1_funct_1(sK3)) )),
% 4.41/0.96    inference(subsumption_resolution,[],[f640,f68])).
% 4.41/0.96  fof(f640,plain,(
% 4.41/0.96    ( ! [X0] : (~r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X0,sK2,sK2) | ~v1_funct_1(X0) | sK4 = X0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK3)) )),
% 4.41/0.96    inference(duplicate_literal_removal,[],[f639])).
% 4.41/0.96  fof(f639,plain,(
% 4.41/0.96    ( ! [X0] : (~r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X0,sK2,sK2) | ~v1_funct_1(X0) | sK4 = X0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(X0)) )),
% 4.41/0.96    inference(superposition,[],[f628,f114])).
% 4.41/0.96  fof(f628,plain,(
% 4.41/0.96    ( ! [X4] : (~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X4,sK3),sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X4,sK2,sK2) | ~v1_funct_1(X4) | sK4 = X4) )),
% 4.41/0.96    inference(forward_demodulation,[],[f627,f233])).
% 4.41/0.96  fof(f233,plain,(
% 4.41/0.96    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 4.41/0.96    inference(subsumption_resolution,[],[f232,f69])).
% 4.41/0.96  fof(f69,plain,(
% 4.41/0.96    v1_funct_1(sK4)),
% 4.41/0.96    inference(cnf_transformation,[],[f57])).
% 4.41/0.96  fof(f232,plain,(
% 4.41/0.96    ~v1_funct_1(sK4) | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 4.41/0.96    inference(subsumption_resolution,[],[f231,f71])).
% 4.41/0.96  fof(f231,plain,(
% 4.41/0.96    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4) | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 4.41/0.96    inference(subsumption_resolution,[],[f230,f66])).
% 4.41/0.96  fof(f230,plain,(
% 4.41/0.96    ~v1_funct_1(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4) | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 4.41/0.96    inference(subsumption_resolution,[],[f226,f68])).
% 4.41/0.96  fof(f226,plain,(
% 4.41/0.96    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4) | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 4.41/0.96    inference(resolution,[],[f116,f187])).
% 4.41/0.96  fof(f187,plain,(
% 4.41/0.96    ~m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 4.41/0.96    inference(subsumption_resolution,[],[f180,f68])).
% 4.41/0.96  fof(f180,plain,(
% 4.41/0.96    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 4.41/0.96    inference(resolution,[],[f112,f72])).
% 4.41/0.96  fof(f72,plain,(
% 4.41/0.96    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3)),
% 4.41/0.96    inference(cnf_transformation,[],[f57])).
% 4.41/0.96  fof(f627,plain,(
% 4.41/0.96    ( ! [X4] : (~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X4,sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)) | k1_xboole_0 = sK2 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X4,sK2,sK2) | ~v1_funct_1(X4) | sK4 = X4) )),
% 4.41/0.96    inference(subsumption_resolution,[],[f626,f69])).
% 4.41/0.96  fof(f626,plain,(
% 4.41/0.96    ( ! [X4] : (~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X4,sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)) | k1_xboole_0 = sK2 | ~v1_funct_1(sK4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X4,sK2,sK2) | ~v1_funct_1(X4) | sK4 = X4) )),
% 4.41/0.96    inference(subsumption_resolution,[],[f619,f71])).
% 4.41/0.96  fof(f619,plain,(
% 4.41/0.96    ( ! [X4] : (~r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X4,sK3),k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | k1_xboole_0 = sK2 | ~v1_funct_1(sK4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X4,sK2,sK2) | ~v1_funct_1(X4) | sK4 = X4) )),
% 4.41/0.96    inference(resolution,[],[f611,f70])).
% 4.41/0.96  fof(f70,plain,(
% 4.41/0.96    v1_funct_2(sK4,sK2,sK2)),
% 4.41/0.96    inference(cnf_transformation,[],[f57])).
% 4.41/0.96  fof(f611,plain,(
% 4.41/0.96    ( ! [X8,X7,X9] : (~v1_funct_2(X9,X7,sK2) | ~r2_relset_1(X7,sK2,k1_partfun1(X7,sK2,sK2,sK2,X8,sK3),k1_partfun1(X7,sK2,sK2,sK2,X9,sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,sK2))) | k1_xboole_0 = sK2 | ~v1_funct_1(X9) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK2))) | ~v1_funct_2(X8,X7,sK2) | ~v1_funct_1(X8) | X8 = X9) )),
% 4.41/0.96    inference(subsumption_resolution,[],[f610,f67])).
% 4.41/0.96  fof(f67,plain,(
% 4.41/0.96    v1_funct_2(sK3,sK2,sK2)),
% 4.41/0.96    inference(cnf_transformation,[],[f57])).
% 4.41/0.96  fof(f610,plain,(
% 4.41/0.96    ( ! [X8,X7,X9] : (k1_xboole_0 = sK2 | ~r2_relset_1(X7,sK2,k1_partfun1(X7,sK2,sK2,sK2,X8,sK3),k1_partfun1(X7,sK2,sK2,sK2,X9,sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,sK2))) | ~v1_funct_2(X9,X7,sK2) | ~v1_funct_1(X9) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK2))) | ~v1_funct_2(X8,X7,sK2) | ~v1_funct_1(X8) | ~v1_funct_2(sK3,sK2,sK2) | X8 = X9) )),
% 4.41/0.96    inference(duplicate_literal_removal,[],[f604])).
% 4.41/0.96  fof(f604,plain,(
% 4.41/0.96    ( ! [X8,X7,X9] : (k1_xboole_0 = sK2 | k1_xboole_0 = sK2 | ~r2_relset_1(X7,sK2,k1_partfun1(X7,sK2,sK2,sK2,X8,sK3),k1_partfun1(X7,sK2,sK2,sK2,X9,sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,sK2))) | ~v1_funct_2(X9,X7,sK2) | ~v1_funct_1(X9) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK2))) | ~v1_funct_2(X8,X7,sK2) | ~v1_funct_1(X8) | ~v1_funct_2(sK3,sK2,sK2) | X8 = X9) )),
% 4.41/0.96    inference(resolution,[],[f518,f68])).
% 4.41/0.96  fof(f518,plain,(
% 4.41/0.96    ( ! [X6,X8,X7,X5,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | k1_xboole_0 = X5 | k1_xboole_0 = X6 | ~r2_relset_1(X7,X6,k1_partfun1(X7,X5,X5,X6,X8,sK3),k1_partfun1(X7,X5,X5,X6,X9,sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X5))) | ~v1_funct_2(X9,X7,X5) | ~v1_funct_1(X9) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,X5))) | ~v1_funct_2(X8,X7,X5) | ~v1_funct_1(X8) | ~v1_funct_2(sK3,X5,X6) | X8 = X9) )),
% 4.41/0.96    inference(duplicate_literal_removal,[],[f517])).
% 4.41/0.96  fof(f517,plain,(
% 4.41/0.96    ( ! [X6,X8,X7,X5,X9] : (~v1_funct_2(sK3,X5,X6) | k1_xboole_0 = X5 | k1_xboole_0 = X6 | ~r2_relset_1(X7,X6,k1_partfun1(X7,X5,X5,X6,X8,sK3),k1_partfun1(X7,X5,X5,X6,X9,sK3)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X5))) | ~v1_funct_2(X9,X7,X5) | ~v1_funct_1(X9) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,X5))) | ~v1_funct_2(X8,X7,X5) | ~v1_funct_1(X8) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | X8 = X9 | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X5))) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,X5)))) )),
% 4.41/0.96    inference(resolution,[],[f395,f112])).
% 4.41/0.96  fof(f395,plain,(
% 4.41/0.96    ( ! [X4,X2,X0,X3,X1] : (r2_relset_1(X2,X0,X3,X4) | ~v1_funct_2(sK3,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | ~r2_relset_1(X2,X1,k1_partfun1(X2,X0,X0,X1,X3,sK3),k1_partfun1(X2,X0,X0,X1,X4,sK3)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_2(X4,X2,X0) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_2(X3,X2,X0) | ~v1_funct_1(X3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.41/0.96    inference(subsumption_resolution,[],[f393,f66])).
% 4.41/0.96  fof(f393,plain,(
% 4.41/0.96    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1) | ~v1_funct_1(sK3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | ~r2_relset_1(X2,X1,k1_partfun1(X2,X0,X0,X1,X3,sK3),k1_partfun1(X2,X0,X0,X1,X4,sK3)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_2(X4,X2,X0) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_2(X3,X2,X0) | ~v1_funct_1(X3) | r2_relset_1(X2,X0,X3,X4)) )),
% 4.41/0.96    inference(resolution,[],[f288,f73])).
% 4.41/0.96  fof(f73,plain,(
% 4.41/0.96    v2_funct_1(sK3)),
% 4.41/0.96    inference(cnf_transformation,[],[f57])).
% 4.41/0.96  fof(f288,plain,(
% 4.41/0.96    ( ! [X4,X2,X0,X5,X3,X1] : (~v2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X1,X0,X2) | ~v1_funct_1(X1) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~r2_relset_1(X3,X2,k1_partfun1(X3,X0,X0,X2,X4,X1),k1_partfun1(X3,X0,X0,X2,X5,X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4) | r2_relset_1(X3,X0,X4,X5)) )),
% 4.41/0.96    inference(resolution,[],[f191,f101])).
% 4.41/0.96  fof(f101,plain,(
% 4.41/0.96    ( ! [X6,X2,X0,X8,X7,X1] : (~sP0(X0,X1,X2) | ~r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X8,X6,X0) | ~v1_funct_1(X8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X7,X6,X0) | ~v1_funct_1(X7) | r2_relset_1(X6,X0,X7,X8)) )),
% 4.41/0.96    inference(cnf_transformation,[],[f64])).
% 4.41/0.96  fof(f64,plain,(
% 4.41/0.96    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK7(X0,X1,X2),X1)) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(sK7(X0,X1,X2),sK5(X0,X1,X2),X0) & v1_funct_1(sK7(X0,X1,X2))) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(sK6(X0,X1,X2),sK5(X0,X1,X2),X0) & v1_funct_1(sK6(X0,X1,X2)))) & (! [X6,X7] : (! [X8] : (r2_relset_1(X6,X0,X7,X8) | ~r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X8,X6,X0) | ~v1_funct_1(X8)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X7,X6,X0) | ~v1_funct_1(X7)) | ~sP0(X0,X1,X2)))),
% 4.41/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f61,f63,f62])).
% 4.41/0.96  fof(f62,plain,(
% 4.41/0.96    ! [X2,X1,X0] : (? [X3,X4] : (? [X5] : (~r2_relset_1(X3,X0,X4,X5) & r2_relset_1(X3,X2,k1_partfun1(X3,X0,X0,X2,X4,X1),k1_partfun1(X3,X0,X0,X2,X5,X1)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X5,X3,X0) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X4,X3,X0) & v1_funct_1(X4)) => (? [X5] : (~r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),X5) & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,X5,X1)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(X5,sK5(X0,X1,X2),X0) & v1_funct_1(X5)) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(sK6(X0,X1,X2),sK5(X0,X1,X2),X0) & v1_funct_1(sK6(X0,X1,X2))))),
% 4.41/0.96    introduced(choice_axiom,[])).
% 4.41/0.96  fof(f63,plain,(
% 4.41/0.96    ! [X2,X1,X0] : (? [X5] : (~r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),X5) & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,X5,X1)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(X5,sK5(X0,X1,X2),X0) & v1_funct_1(X5)) => (~r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK7(X0,X1,X2),X1)) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(sK7(X0,X1,X2),sK5(X0,X1,X2),X0) & v1_funct_1(sK7(X0,X1,X2))))),
% 4.41/0.96    introduced(choice_axiom,[])).
% 4.41/0.96  fof(f61,plain,(
% 4.41/0.96    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3,X4] : (? [X5] : (~r2_relset_1(X3,X0,X4,X5) & r2_relset_1(X3,X2,k1_partfun1(X3,X0,X0,X2,X4,X1),k1_partfun1(X3,X0,X0,X2,X5,X1)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X5,X3,X0) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X4,X3,X0) & v1_funct_1(X4))) & (! [X6,X7] : (! [X8] : (r2_relset_1(X6,X0,X7,X8) | ~r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X8,X6,X0) | ~v1_funct_1(X8)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X7,X6,X0) | ~v1_funct_1(X7)) | ~sP0(X0,X1,X2)))),
% 4.41/0.96    inference(rectify,[],[f60])).
% 4.41/0.96  fof(f60,plain,(
% 4.41/0.96    ! [X0,X2,X1] : ((sP0(X0,X2,X1) | ? [X3,X4] : (? [X5] : (~r2_relset_1(X3,X0,X4,X5) & r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X5,X3,X0) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X4,X3,X0) & v1_funct_1(X4))) & (! [X3,X4] : (! [X5] : (r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4)) | ~sP0(X0,X2,X1)))),
% 4.41/0.96    inference(nnf_transformation,[],[f52])).
% 4.41/0.96  fof(f52,plain,(
% 4.41/0.96    ! [X0,X2,X1] : (sP0(X0,X2,X1) <=> ! [X3,X4] : (! [X5] : (r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4)))),
% 4.41/0.96    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 4.41/0.96  fof(f191,plain,(
% 4.41/0.96    ( ! [X2,X0,X1] : (sP0(X1,X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X1,X0) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X0) )),
% 4.41/0.96    inference(resolution,[],[f110,f99])).
% 4.41/0.96  fof(f99,plain,(
% 4.41/0.96    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~v2_funct_1(X1) | sP0(X2,X1,X0)) )),
% 4.41/0.96    inference(cnf_transformation,[],[f59])).
% 4.41/0.96  fof(f59,plain,(
% 4.41/0.96    ! [X0,X1,X2] : (((v2_funct_1(X1) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~v2_funct_1(X1))) | ~sP1(X0,X1,X2))),
% 4.41/0.96    inference(rectify,[],[f58])).
% 4.41/0.96  fof(f58,plain,(
% 4.41/0.96    ! [X1,X2,X0] : (((v2_funct_1(X2) | ~sP0(X0,X2,X1)) & (sP0(X0,X2,X1) | ~v2_funct_1(X2))) | ~sP1(X1,X2,X0))),
% 4.41/0.96    inference(nnf_transformation,[],[f53])).
% 4.41/0.96  fof(f53,plain,(
% 4.41/0.96    ! [X1,X2,X0] : ((v2_funct_1(X2) <=> sP0(X0,X2,X1)) | ~sP1(X1,X2,X0))),
% 4.41/0.96    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 4.41/0.96  fof(f110,plain,(
% 4.41/0.96    ( ! [X2,X0,X1] : (sP1(X1,X2,X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 4.41/0.96    inference(cnf_transformation,[],[f54])).
% 4.41/0.96  fof(f54,plain,(
% 4.41/0.96    ! [X0,X1,X2] : (sP1(X1,X2,X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 4.41/0.96    inference(definition_folding,[],[f41,f53,f52])).
% 4.41/0.96  fof(f41,plain,(
% 4.41/0.96    ! [X0,X1,X2] : ((v2_funct_1(X2) <=> ! [X3,X4] : (! [X5] : (r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4))) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 4.41/0.96    inference(flattening,[],[f40])).
% 4.41/0.96  fof(f40,plain,(
% 4.41/0.96    ! [X0,X1,X2] : (((v2_funct_1(X2) <=> ! [X3,X4] : (! [X5] : ((r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4)))) | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 4.41/0.96    inference(ennf_transformation,[],[f18])).
% 4.41/0.96  fof(f18,axiom,(
% 4.41/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ~(~(v2_funct_1(X2) <=> ! [X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X4,X3,X0) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X5,X3,X0) & v1_funct_1(X5)) => (r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) => r2_relset_1(X3,X0,X4,X5))))) & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 4.41/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_2)).
% 4.41/0.96  fof(f855,plain,(
% 4.41/0.96    v1_funct_2(k6_partfun1(sK2),sK2,sK2)),
% 4.41/0.96    inference(resolution,[],[f816,f79])).
% 4.41/0.96  fof(f816,plain,(
% 4.41/0.96    ( ! [X0,X1] : (~m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(k6_partfun1(sK2),sK2,sK2)) )),
% 4.41/0.96    inference(resolution,[],[f810,f151])).
% 4.41/0.96  fof(f151,plain,(
% 4.41/0.96    ( ! [X2,X0,X1] : (~v1_funct_1(k6_partfun1(X0)) | ~m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_funct_2(k6_partfun1(X0),X0,X0)) )),
% 4.41/0.96    inference(forward_demodulation,[],[f147,f119])).
% 4.41/0.96  fof(f119,plain,(
% 4.41/0.96    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 4.41/0.96    inference(definition_unfolding,[],[f81,f77])).
% 4.41/0.96  fof(f81,plain,(
% 4.41/0.96    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 4.41/0.96    inference(cnf_transformation,[],[f6])).
% 4.41/0.96  fof(f6,axiom,(
% 4.41/0.96    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 4.41/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 4.41/0.96  fof(f147,plain,(
% 4.41/0.96    ( ! [X2,X0,X1] : (v1_funct_2(k6_partfun1(X0),X0,k2_relat_1(k6_partfun1(X0))) | ~m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(k6_partfun1(X0))) )),
% 4.41/0.96    inference(superposition,[],[f145,f120])).
% 4.41/0.96  fof(f120,plain,(
% 4.41/0.96    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 4.41/0.96    inference(definition_unfolding,[],[f80,f77])).
% 4.41/0.96  fof(f80,plain,(
% 4.41/0.96    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 4.41/0.96    inference(cnf_transformation,[],[f6])).
% 4.41/0.96  fof(f145,plain,(
% 4.41/0.96    ( ! [X2,X0,X1] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0)) )),
% 4.41/0.96    inference(resolution,[],[f134,f90])).
% 4.41/0.96  fof(f90,plain,(
% 4.41/0.96    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 4.41/0.96    inference(cnf_transformation,[],[f4])).
% 4.41/0.96  fof(f4,axiom,(
% 4.41/0.96    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 4.41/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 4.41/0.96  fof(f134,plain,(
% 4.41/0.96    ( ! [X2,X3] : (~v1_relat_1(X3) | v1_funct_2(X2,k1_relat_1(X2),k2_relat_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X3)) | ~v1_funct_1(X2)) )),
% 4.41/0.96    inference(resolution,[],[f86,f84])).
% 4.41/0.97  fof(f84,plain,(
% 4.41/0.97    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 4.41/0.97    inference(cnf_transformation,[],[f28])).
% 4.41/0.97  fof(f28,plain,(
% 4.41/0.97    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 4.41/0.97    inference(ennf_transformation,[],[f3])).
% 4.41/0.97  fof(f3,axiom,(
% 4.41/0.97    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 4.41/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 4.41/0.97  fof(f86,plain,(
% 4.41/0.97    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 4.41/0.97    inference(cnf_transformation,[],[f30])).
% 4.41/0.97  fof(f30,plain,(
% 4.41/0.97    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.41/0.97    inference(flattening,[],[f29])).
% 4.41/0.97  fof(f29,plain,(
% 4.41/0.97    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.41/0.97    inference(ennf_transformation,[],[f20])).
% 4.41/0.97  fof(f20,axiom,(
% 4.41/0.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 4.41/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 4.41/0.97  fof(f74,plain,(
% 4.41/0.97    ~r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2))),
% 4.41/0.97    inference(cnf_transformation,[],[f57])).
% 4.41/0.97  fof(f810,plain,(
% 4.41/0.97    v1_funct_1(k6_partfun1(sK2))),
% 4.41/0.97    inference(resolution,[],[f803,f68])).
% 4.41/0.97  fof(f803,plain,(
% 4.41/0.97    ( ! [X6,X7] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | v1_funct_1(k6_partfun1(sK2))) )),
% 4.41/0.97    inference(resolution,[],[f796,f68])).
% 4.41/0.97  fof(f796,plain,(
% 4.41/0.97    ( ! [X10,X8,X11,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | v1_funct_1(k6_partfun1(sK2))) )),
% 4.41/0.97    inference(resolution,[],[f788,f68])).
% 4.41/0.97  fof(f788,plain,(
% 4.41/0.97    ( ! [X14,X12,X10,X15,X13,X11] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) | v1_funct_1(k6_partfun1(sK2))) )),
% 4.41/0.97    inference(resolution,[],[f786,f68])).
% 4.41/0.97  fof(f786,plain,(
% 4.41/0.97    ( ! [X57,X54,X52,X58,X56,X55,X53,X51] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X57,X58))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X53,X54))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) | v1_funct_1(k6_partfun1(sK2))) )),
% 4.41/0.97    inference(subsumption_resolution,[],[f781,f179])).
% 4.41/0.97  fof(f179,plain,(
% 4.41/0.97    ( ! [X0,X1] : (v1_funct_2(sK3,sK2,k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.41/0.97    inference(subsumption_resolution,[],[f177,f66])).
% 4.41/0.97  fof(f177,plain,(
% 4.41/0.97    ( ! [X0,X1] : (v1_funct_2(sK3,sK2,k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK3)) )),
% 4.41/0.97    inference(superposition,[],[f145,f174])).
% 4.41/0.97  fof(f174,plain,(
% 4.41/0.97    sK2 = k1_relat_1(sK3)),
% 4.41/0.97    inference(subsumption_resolution,[],[f173,f66])).
% 4.41/0.97  fof(f173,plain,(
% 4.41/0.97    sK2 = k1_relat_1(sK3) | ~v1_funct_1(sK3)),
% 4.41/0.97    inference(subsumption_resolution,[],[f170,f68])).
% 4.41/0.97  fof(f170,plain,(
% 4.41/0.97    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | sK2 = k1_relat_1(sK3) | ~v1_funct_1(sK3)),
% 4.41/0.97    inference(resolution,[],[f162,f67])).
% 4.41/0.97  fof(f162,plain,(
% 4.41/0.97    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relat_1(X1) = X0 | ~v1_funct_1(X1)) )),
% 4.41/0.97    inference(duplicate_literal_removal,[],[f159])).
% 4.41/0.97  fof(f159,plain,(
% 4.41/0.97    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 4.41/0.97    inference(superposition,[],[f91,f92])).
% 4.41/0.97  fof(f92,plain,(
% 4.41/0.97    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.41/0.97    inference(cnf_transformation,[],[f35])).
% 4.41/0.97  fof(f35,plain,(
% 4.41/0.97    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.41/0.97    inference(ennf_transformation,[],[f9])).
% 4.41/0.97  fof(f9,axiom,(
% 4.41/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 4.41/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 4.41/0.97  fof(f91,plain,(
% 4.41/0.97    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 4.41/0.97    inference(cnf_transformation,[],[f34])).
% 4.41/0.97  fof(f34,plain,(
% 4.41/0.97    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 4.41/0.97    inference(flattening,[],[f33])).
% 4.41/0.97  fof(f33,plain,(
% 4.41/0.97    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 4.41/0.97    inference(ennf_transformation,[],[f21])).
% 4.41/0.97  fof(f21,axiom,(
% 4.41/0.97    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 4.41/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).
% 4.41/0.97  fof(f781,plain,(
% 4.41/0.97    ( ! [X57,X54,X52,X58,X56,X55,X53,X51] : (v1_funct_1(k6_partfun1(sK2)) | ~v1_funct_2(sK3,sK2,k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X53,X54))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))) )),
% 4.41/0.97    inference(resolution,[],[f773,f268])).
% 4.41/0.97  fof(f268,plain,(
% 4.41/0.97    ( ! [X14,X13] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) )),
% 4.41/0.97    inference(forward_demodulation,[],[f264,f174])).
% 4.41/0.97  fof(f264,plain,(
% 4.41/0.97    ( ! [X14,X13] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))) )),
% 4.41/0.97    inference(resolution,[],[f167,f66])).
% 4.41/0.97  fof(f167,plain,(
% 4.41/0.97    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 4.41/0.97    inference(resolution,[],[f136,f90])).
% 4.41/0.97  fof(f136,plain,(
% 4.41/0.97    ( ! [X2,X3] : (~v1_relat_1(X3) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(X3)) | ~v1_funct_1(X2)) )),
% 4.41/0.97    inference(resolution,[],[f87,f84])).
% 4.41/0.97  fof(f87,plain,(
% 4.41/0.97    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 4.41/0.97    inference(cnf_transformation,[],[f30])).
% 4.41/0.97  fof(f773,plain,(
% 4.41/0.97    ( ! [X47,X52,X50,X48,X46,X51,X49] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X46,k2_relat_1(sK3)))) | v1_funct_1(k6_partfun1(sK2)) | ~v1_funct_2(sK3,X46,k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))) )),
% 4.41/0.97    inference(subsumption_resolution,[],[f768,f179])).
% 4.41/0.97  fof(f768,plain,(
% 4.41/0.97    ( ! [X47,X52,X50,X48,X46,X51,X49] : (~v1_funct_2(sK3,sK2,k2_relat_1(sK3)) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X46,k2_relat_1(sK3)))) | ~v1_funct_2(sK3,X46,k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))) )),
% 4.41/0.97    inference(resolution,[],[f760,f268])).
% 4.41/0.97  fof(f760,plain,(
% 4.41/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3)))) | ~v1_funct_2(sK3,X0,k2_relat_1(sK3)) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(sK3)))) | ~v1_funct_2(sK3,X1,k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 4.41/0.97    inference(equality_resolution,[],[f759])).
% 4.41/0.97  fof(f759,plain,(
% 4.41/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_relat_1(sK3) != X1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(sK3)))) | ~v1_funct_2(sK3,X2,k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) )),
% 4.41/0.97    inference(equality_resolution,[],[f753])).
% 4.41/0.97  fof(f753,plain,(
% 4.41/0.97    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_relat_1(sK3) != X1 | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(sK3,X2,X3) | k2_relat_1(sK3) != X3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) )),
% 4.41/0.97    inference(duplicate_literal_removal,[],[f752])).
% 4.41/0.97  fof(f752,plain,(
% 4.41/0.97    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_relat_1(sK3) != X1 | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(sK3,X2,X3) | k2_relat_1(sK3) != X3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.41/0.97    inference(superposition,[],[f747,f93])).
% 4.41/0.97  fof(f93,plain,(
% 4.41/0.97    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.41/0.97    inference(cnf_transformation,[],[f36])).
% 4.41/0.97  fof(f36,plain,(
% 4.41/0.97    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.41/0.97    inference(ennf_transformation,[],[f10])).
% 4.41/0.97  fof(f10,axiom,(
% 4.41/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 4.41/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 4.41/0.97  fof(f747,plain,(
% 4.41/0.97    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_relset_1(X2,X3,sK3) != X3 | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1) | k2_relat_1(sK3) != X1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(sK3,X2,X3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) )),
% 4.41/0.97    inference(duplicate_literal_removal,[],[f746])).
% 4.41/0.97  fof(f746,plain,(
% 4.41/0.97    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_relat_1(sK3) != X1 | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1) | k2_relset_1(X2,X3,sK3) != X3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(sK3,X2,X3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.41/0.97    inference(superposition,[],[f744,f93])).
% 4.41/0.97  fof(f744,plain,(
% 4.41/0.97    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_relset_1(X0,X1,sK3) != X1 | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1) | k2_relset_1(X2,X3,sK3) != X3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(sK3,X2,X3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) )),
% 4.41/0.97    inference(resolution,[],[f719,f90])).
% 4.41/0.97  fof(f719,plain,(
% 4.41/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~v1_relat_1(X6) | v1_funct_1(k6_partfun1(sK2)) | k2_relset_1(X2,X3,sK3) != X3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(sK3,X2,X3) | k2_relset_1(X4,X5,sK3) != X5 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_2(sK3,X4,X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X6)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.41/0.97    inference(resolution,[],[f690,f84])).
% 4.41/0.97  fof(f690,plain,(
% 4.41/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k6_partfun1(sK2)) | k2_relset_1(X2,X3,sK3) != X3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(sK3,X2,X3) | k2_relset_1(X4,X5,sK3) != X5 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_2(sK3,X4,X5)) )),
% 4.41/0.97    inference(forward_demodulation,[],[f689,f174])).
% 4.41/0.97  fof(f689,plain,(
% 4.41/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k6_partfun1(k1_relat_1(sK3))) | ~v1_relat_1(sK3) | k2_relset_1(X2,X3,sK3) != X3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(sK3,X2,X3) | k2_relset_1(X4,X5,sK3) != X5 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_2(sK3,X4,X5)) )),
% 4.41/0.97    inference(subsumption_resolution,[],[f687,f66])).
% 4.41/0.97  fof(f687,plain,(
% 4.41/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK3) | v1_funct_1(k6_partfun1(k1_relat_1(sK3))) | ~v1_relat_1(sK3) | k2_relset_1(X2,X3,sK3) != X3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(sK3,X2,X3) | k2_relset_1(X4,X5,sK3) != X5 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_2(sK3,X4,X5)) )),
% 4.41/0.97    inference(resolution,[],[f499,f73])).
% 4.41/0.97  fof(f499,plain,(
% 4.41/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~v2_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | v1_funct_1(k6_partfun1(k1_relat_1(X0))) | ~v1_relat_1(X0) | k2_relset_1(X3,X4,X0) != X4 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X0,X3,X4) | k2_relset_1(X5,X6,X0) != X6 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(X0,X5,X6)) )),
% 4.41/0.97    inference(duplicate_literal_removal,[],[f496])).
% 4.41/0.97  fof(f496,plain,(
% 4.41/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_funct_1(k6_partfun1(k1_relat_1(X0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0) | k2_relset_1(X3,X4,X0) != X4 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X0,X3,X4) | k2_relset_1(X5,X6,X0) != X6 | ~v2_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(X0,X5,X6) | ~v1_funct_1(X0)) )),
% 4.41/0.97    inference(resolution,[],[f360,f98])).
% 4.41/0.97  fof(f98,plain,(
% 4.41/0.97    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 4.41/0.97    inference(cnf_transformation,[],[f39])).
% 4.41/0.97  fof(f39,plain,(
% 4.41/0.97    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 4.41/0.97    inference(flattening,[],[f38])).
% 4.41/0.97  fof(f38,plain,(
% 4.41/0.97    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 4.41/0.97    inference(ennf_transformation,[],[f19])).
% 4.41/0.97  fof(f19,axiom,(
% 4.41/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 4.41/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 4.41/0.97  fof(f360,plain,(
% 4.41/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_funct_1(k6_partfun1(k1_relat_1(X0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0) | k2_relset_1(X5,X6,X0) != X6 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(X0,X5,X6)) )),
% 4.41/0.97    inference(duplicate_literal_removal,[],[f359])).
% 4.41/0.97  fof(f359,plain,(
% 4.41/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_funct_1(k6_partfun1(k1_relat_1(X0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0) | k2_relset_1(X5,X6,X0) != X6 | ~v2_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(X0,X5,X6) | ~v1_funct_1(X0)) )),
% 4.41/0.97    inference(resolution,[],[f280,f96])).
% 4.41/0.97  fof(f96,plain,(
% 4.41/0.97    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 4.41/0.97    inference(cnf_transformation,[],[f39])).
% 4.41/0.97  fof(f280,plain,(
% 4.41/0.97    ( ! [X6,X8,X7,X5,X9] : (~v1_funct_1(k2_funct_1(X5)) | ~m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | v1_funct_1(k6_partfun1(k1_relat_1(X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_1(X5) | ~v2_funct_1(X5) | ~v1_relat_1(X5)) )),
% 4.41/0.97    inference(duplicate_literal_removal,[],[f278])).
% 4.41/0.97  fof(f278,plain,(
% 4.41/0.97    ( ! [X6,X8,X7,X5,X9] : (v1_funct_1(k6_partfun1(k1_relat_1(X5))) | ~m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_1(k2_funct_1(X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_1(X5) | ~v2_funct_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(X5)) )),
% 4.41/0.97    inference(superposition,[],[f216,f122])).
% 4.41/0.97  fof(f122,plain,(
% 4.41/0.97    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.41/0.97    inference(definition_unfolding,[],[f88,f77])).
% 4.41/0.97  fof(f88,plain,(
% 4.41/0.97    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.41/0.97    inference(cnf_transformation,[],[f32])).
% 4.41/0.97  fof(f32,plain,(
% 4.41/0.97    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.41/0.97    inference(flattening,[],[f31])).
% 4.41/0.97  fof(f31,plain,(
% 4.41/0.97    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.41/0.97    inference(ennf_transformation,[],[f8])).
% 4.41/0.97  fof(f8,axiom,(
% 4.41/0.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 4.41/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 4.41/0.97  fof(f216,plain,(
% 4.41/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k5_relat_1(X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 4.41/0.97    inference(duplicate_literal_removal,[],[f215])).
% 4.41/0.97  fof(f215,plain,(
% 4.41/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k5_relat_1(X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 4.41/0.97    inference(superposition,[],[f115,f114])).
% 4.41/0.97  fof(f115,plain,(
% 4.41/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 4.41/0.97    inference(cnf_transformation,[],[f49])).
% 4.41/0.97  fof(f204,plain,(
% 4.41/0.97    ( ! [X0] : (r2_relset_1(k1_xboole_0,X0,k5_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)) )),
% 4.41/0.97    inference(resolution,[],[f199,f76])).
% 4.41/0.97  fof(f199,plain,(
% 4.41/0.97    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | r2_relset_1(k1_xboole_0,X0,k5_relat_1(k1_xboole_0,X1),X1)) )),
% 4.41/0.97    inference(superposition,[],[f196,f118])).
% 4.41/0.97  fof(f1254,plain,(
% 4.41/0.97    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 4.41/0.97    inference(backward_demodulation,[],[f1062,f1234])).
% 4.41/0.97  fof(f1234,plain,(
% 4.41/0.97    k1_xboole_0 = sK4),
% 4.41/0.97    inference(resolution,[],[f1060,f972])).
% 4.41/0.97  fof(f972,plain,(
% 4.41/0.97    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 4.41/0.97    inference(backward_demodulation,[],[f71,f968])).
% 4.41/0.97  fof(f1060,plain,(
% 4.41/0.97    ( ! [X2,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = sK4) )),
% 4.41/0.97    inference(trivial_inequality_removal,[],[f978])).
% 4.41/0.97  fof(f978,plain,(
% 4.41/0.97    ( ! [X2,X3] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = sK4) )),
% 4.41/0.97    inference(backward_demodulation,[],[f189,f968])).
% 4.41/0.97  fof(f189,plain,(
% 4.41/0.97    ( ! [X2,X3] : (k1_xboole_0 != sK2 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = sK4) )),
% 4.41/0.97    inference(superposition,[],[f137,f176])).
% 4.41/0.97  fof(f176,plain,(
% 4.41/0.97    sK2 = k1_relat_1(sK4)),
% 4.41/0.97    inference(subsumption_resolution,[],[f175,f69])).
% 4.41/0.97  fof(f175,plain,(
% 4.41/0.97    sK2 = k1_relat_1(sK4) | ~v1_funct_1(sK4)),
% 4.41/0.97    inference(subsumption_resolution,[],[f171,f71])).
% 4.41/0.97  fof(f171,plain,(
% 4.41/0.97    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | sK2 = k1_relat_1(sK4) | ~v1_funct_1(sK4)),
% 4.41/0.97    inference(resolution,[],[f162,f70])).
% 4.41/0.97  fof(f137,plain,(
% 4.41/0.97    ( ! [X2,X0,X1] : (k1_xboole_0 != k1_relat_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = X0) )),
% 4.41/0.97    inference(resolution,[],[f130,f90])).
% 4.41/0.97  fof(f130,plain,(
% 4.41/0.97    ( ! [X2,X3] : (~v1_relat_1(X3) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(X3)) | k1_xboole_0 != k1_relat_1(X2)) )),
% 4.41/0.97    inference(resolution,[],[f82,f84])).
% 4.41/0.97  fof(f82,plain,(
% 4.41/0.97    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 4.41/0.97    inference(cnf_transformation,[],[f27])).
% 4.41/0.97  fof(f27,plain,(
% 4.41/0.97    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 4.41/0.97    inference(flattening,[],[f26])).
% 4.41/0.97  fof(f26,plain,(
% 4.41/0.97    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 4.41/0.97    inference(ennf_transformation,[],[f5])).
% 4.41/0.97  fof(f5,axiom,(
% 4.41/0.97    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 4.41/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 4.41/0.97  fof(f1062,plain,(
% 4.41/0.97    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k1_xboole_0)),
% 4.41/0.97    inference(forward_demodulation,[],[f973,f118])).
% 4.41/0.97  fof(f973,plain,(
% 4.41/0.97    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k6_partfun1(k1_xboole_0))),
% 4.41/0.97    inference(backward_demodulation,[],[f74,f968])).
% 4.41/0.97  % SZS output end Proof for theBenchmark
% 4.41/0.97  % (23639)------------------------------
% 4.41/0.97  % (23639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.41/0.97  % (23639)Termination reason: Refutation
% 4.41/0.97  
% 4.41/0.97  % (23639)Memory used [KB]: 8955
% 4.41/0.97  % (23639)Time elapsed: 0.522 s
% 4.41/0.97  % (23639)------------------------------
% 4.41/0.97  % (23639)------------------------------
% 4.41/0.97  % (23616)Success in time 0.598 s
%------------------------------------------------------------------------------
