%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:26 EST 2020

% Result     : Theorem 13.68s
% Output     : Refutation 13.68s
% Verified   : 
% Statistics : Number of formulae       :  247 (12235 expanded)
%              Number of leaves         :   29 (3594 expanded)
%              Depth                    :   45
%              Number of atoms          : 1099 (91778 expanded)
%              Number of equality atoms :  191 (3891 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6283,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6030,f5528])).

fof(f5528,plain,(
    ! [X0] : r2_relset_1(k1_xboole_0,X0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f445,f5525])).

fof(f5525,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f5301,f5241])).

fof(f5241,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f70,f5240])).

fof(f5240,plain,(
    k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f5239,f138])).

fof(f138,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
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

fof(f5239,plain,(
    sK3 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f5238,f4688])).

fof(f4688,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f4687,f406])).

fof(f406,plain,(
    r2_relset_1(sK2,sK2,sK3,sK3) ),
    inference(backward_demodulation,[],[f76,f404])).

fof(f404,plain,(
    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f403,f73])).

fof(f73,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,
    ( ~ r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2))
    & v2_funct_1(sK3)
    & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK4,sK2,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK3,sK2,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f27,f55,f54])).

fof(f54,plain,
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

fof(f55,plain,
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

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
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
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_funct_2)).

fof(f403,plain,
    ( sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f402,f75])).

fof(f75,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f56])).

fof(f402,plain,
    ( sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f401,f70])).

fof(f401,plain,
    ( sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f398,f72])).

fof(f72,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f56])).

fof(f398,plain,
    ( sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f294,f127])).

fof(f127,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
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
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f294,plain,
    ( ~ m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f287,f72])).

fof(f287,plain,
    ( sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(resolution,[],[f123,f76])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f76,plain,(
    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f4687,plain,
    ( ~ r2_relset_1(sK2,sK2,sK3,sK3)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f4686,f426])).

fof(f426,plain,(
    sK3 = k5_relat_1(sK4,sK3) ),
    inference(subsumption_resolution,[],[f425,f73])).

fof(f425,plain,
    ( sK3 = k5_relat_1(sK4,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f424,f75])).

fof(f424,plain,
    ( sK3 = k5_relat_1(sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f423,f70])).

fof(f423,plain,
    ( sK3 = k5_relat_1(sK4,sK3)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f417,f72])).

fof(f417,plain,
    ( sK3 = k5_relat_1(sK4,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4) ),
    inference(superposition,[],[f404,f125])).

fof(f125,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f4686,plain,
    ( k1_xboole_0 = sK2
    | ~ r2_relset_1(sK2,sK2,k5_relat_1(sK4,sK3),sK3) ),
    inference(subsumption_resolution,[],[f4685,f73])).

fof(f4685,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_funct_1(sK4)
    | ~ r2_relset_1(sK2,sK2,k5_relat_1(sK4,sK3),sK3) ),
    inference(subsumption_resolution,[],[f4684,f74])).

fof(f74,plain,(
    v1_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f4684,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4)
    | ~ r2_relset_1(sK2,sK2,k5_relat_1(sK4,sK3),sK3) ),
    inference(subsumption_resolution,[],[f4683,f75])).

fof(f4683,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4)
    | ~ r2_relset_1(sK2,sK2,k5_relat_1(sK4,sK3),sK3) ),
    inference(duplicate_literal_removal,[],[f4680])).

fof(f4680,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK2
    | ~ r2_relset_1(sK2,sK2,k5_relat_1(sK4,sK3),sK3) ),
    inference(resolution,[],[f4493,f2701])).

fof(f2701,plain,(
    ! [X3] :
      ( r2_relset_1(sK2,sK2,X3,sK4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X3,sK2,sK2)
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = sK2
      | ~ r2_relset_1(sK2,sK2,k5_relat_1(X3,sK3),sK3) ) ),
    inference(subsumption_resolution,[],[f2700,f75])).

fof(f2700,plain,(
    ! [X3] :
      ( ~ r2_relset_1(sK2,sK2,k5_relat_1(X3,sK3),sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X3,sK2,sK2)
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | r2_relset_1(sK2,sK2,X3,sK4) ) ),
    inference(subsumption_resolution,[],[f2699,f74])).

fof(f2699,plain,(
    ! [X3] :
      ( ~ r2_relset_1(sK2,sK2,k5_relat_1(X3,sK3),sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X3,sK2,sK2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(sK4,sK2,sK2)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | r2_relset_1(sK2,sK2,X3,sK4) ) ),
    inference(subsumption_resolution,[],[f2694,f73])).

fof(f2694,plain,(
    ! [X3] :
      ( ~ r2_relset_1(sK2,sK2,k5_relat_1(X3,sK3),sK3)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X3,sK2,sK2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(sK4,sK2,sK2)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | r2_relset_1(sK2,sK2,X3,sK4) ) ),
    inference(superposition,[],[f1529,f404])).

fof(f1529,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_relset_1(X5,sK2,k5_relat_1(X6,sK3),k1_partfun1(X5,sK2,sK2,sK2,X4,sK3))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,sK2)))
      | ~ v1_funct_2(X6,X5,sK2)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X4,X5,sK2)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,sK2)))
      | r2_relset_1(X5,sK2,X6,X4) ) ),
    inference(subsumption_resolution,[],[f1518,f72])).

fof(f1518,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_funct_2(X4,X5,sK2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,sK2)))
      | ~ v1_funct_2(X6,X5,sK2)
      | ~ v1_funct_1(X6)
      | ~ r2_relset_1(X5,sK2,k5_relat_1(X6,sK3),k1_partfun1(X5,sK2,sK2,sK2,X4,sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,sK2)))
      | r2_relset_1(X5,sK2,X6,X4) ) ),
    inference(duplicate_literal_removal,[],[f1516])).

fof(f1516,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_funct_2(X4,X5,sK2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,sK2)))
      | ~ v1_funct_2(X6,X5,sK2)
      | ~ v1_funct_1(X6)
      | ~ r2_relset_1(X5,sK2,k5_relat_1(X6,sK3),k1_partfun1(X5,sK2,sK2,sK2,X4,sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,sK2)))
      | r2_relset_1(X5,sK2,X6,X4)
      | k1_xboole_0 = sK2 ) ),
    inference(resolution,[],[f1033,f71])).

fof(f71,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f1033,plain,(
    ! [X23,X21,X19,X22,X20] :
      ( ~ v1_funct_2(sK3,X21,X23)
      | ~ v1_funct_2(X19,X20,X21)
      | ~ v1_funct_1(X19)
      | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | ~ v1_funct_2(X22,X20,X21)
      | ~ v1_funct_1(X22)
      | ~ r2_relset_1(X20,X23,k5_relat_1(X22,sK3),k1_partfun1(X20,X21,X21,X23,X19,sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X21,X23)))
      | k1_xboole_0 = X21
      | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | r2_relset_1(X20,X21,X22,X19)
      | k1_xboole_0 = X23 ) ),
    inference(subsumption_resolution,[],[f1032,f70])).

fof(f1032,plain,(
    ! [X23,X21,X19,X22,X20] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | ~ v1_funct_2(X19,X20,X21)
      | ~ v1_funct_1(X19)
      | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | ~ v1_funct_2(X22,X20,X21)
      | ~ v1_funct_1(X22)
      | ~ r2_relset_1(X20,X23,k5_relat_1(X22,sK3),k1_partfun1(X20,X21,X21,X23,X19,sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X21,X23)))
      | ~ v1_funct_1(sK3)
      | k1_xboole_0 = X21
      | ~ v1_funct_2(sK3,X21,X23)
      | r2_relset_1(X20,X21,X22,X19)
      | k1_xboole_0 = X23 ) ),
    inference(resolution,[],[f611,f77])).

fof(f77,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f611,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v2_funct_1(X5)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ r2_relset_1(X0,X4,k5_relat_1(X2,X5),k1_partfun1(X0,X1,X1,X4,X3,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
      | ~ v1_funct_1(X5)
      | k1_xboole_0 = X1
      | ~ v1_funct_2(X5,X1,X4)
      | r2_relset_1(X0,X1,X2,X3)
      | k1_xboole_0 = X4 ) ),
    inference(duplicate_literal_removal,[],[f607])).

fof(f607,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ r2_relset_1(X0,X4,k5_relat_1(X2,X5),k1_partfun1(X0,X1,X1,X4,X3,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
      | ~ v1_funct_1(X5)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
      | ~ v1_funct_2(X5,X1,X4)
      | ~ v1_funct_1(X5)
      | ~ v2_funct_1(X5)
      | k1_xboole_0 = X4 ) ),
    inference(resolution,[],[f377,f307])).

fof(f307,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f122,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ v2_funct_1(X1)
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( ( v2_funct_1(X1)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ v2_funct_1(X1) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X1,X2,X0] :
      ( ( ( v2_funct_1(X2)
          | ~ sP0(X0,X2,X1) )
        & ( sP0(X0,X2,X1)
          | ~ v2_funct_1(X2) ) )
      | ~ sP1(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X1,X2,X0] :
      ( ( v2_funct_1(X2)
      <=> sP0(X0,X2,X1) )
      | ~ sP1(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X2,X0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X2,X0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f42,f52,f51])).

fof(f51,plain,(
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

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_2)).

fof(f377,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ sP0(X1,X4,X2)
      | r2_relset_1(X0,X1,X3,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X5,X0,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r2_relset_1(X0,X2,k5_relat_1(X3,X4),k1_partfun1(X0,X1,X1,X2,X5,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f374])).

fof(f374,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_relset_1(X0,X2,k5_relat_1(X3,X4),k1_partfun1(X0,X1,X1,X2,X5,X4))
      | r2_relset_1(X0,X1,X3,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X5,X0,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ sP0(X1,X4,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(superposition,[],[f113,f125])).

fof(f113,plain,(
    ! [X6,X2,X0,X8,X7,X1] :
      ( ~ r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1))
      | r2_relset_1(X6,X0,X7,X8)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0)))
      | ~ v1_funct_2(X8,X6,X0)
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0)))
      | ~ v1_funct_2(X7,X6,X0)
      | ~ v1_funct_1(X7)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f65,f67,f66])).

fof(f66,plain,(
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

fof(f67,plain,(
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

fof(f65,plain,(
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
    inference(rectify,[],[f64])).

fof(f64,plain,(
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
    inference(nnf_transformation,[],[f51])).

fof(f4493,plain,
    ( ~ r2_relset_1(sK2,sK2,sK4,sK4)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f78,f4484])).

fof(f4484,plain,
    ( k6_partfun1(sK2) = sK4
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f4483,f4388])).

fof(f4388,plain,(
    v1_funct_1(k6_partfun1(sK2)) ),
    inference(resolution,[],[f4374,f72])).

fof(f4374,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k6_partfun1(sK2)) ) ),
    inference(resolution,[],[f4373,f1970])).

fof(f1970,plain,(
    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),sK2))) ),
    inference(resolution,[],[f1963,f948])).

fof(f948,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3))))
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),sK2))) ),
    inference(trivial_inequality_removal,[],[f946])).

fof(f946,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3))))
    | k2_relat_1(sK3) != k2_relat_1(sK3)
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),sK2))) ),
    inference(resolution,[],[f618,f136])).

fof(f136,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
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

fof(f618,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK3),X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | k2_relat_1(sK3) != X0
      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) ) ),
    inference(forward_demodulation,[],[f617,f488])).

fof(f488,plain,(
    sK2 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f487,f70])).

fof(f487,plain,
    ( sK2 = k1_relat_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f482,f72])).

fof(f482,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | sK2 = k1_relat_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f252,f71])).

fof(f252,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relat_1(X1) = X0
      | ~ v1_funct_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f249])).

fof(f249,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(superposition,[],[f94,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f94,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f617,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | k2_relat_1(sK3) != X0
      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK3))))
      | ~ r1_tarski(k2_relat_1(sK3),X0) ) ),
    inference(forward_demodulation,[],[f616,f488])).

fof(f616,plain,(
    ! [X0] :
      ( k2_relat_1(sK3) != X0
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK3))))
      | ~ r1_tarski(k2_relat_1(sK3),X0) ) ),
    inference(subsumption_resolution,[],[f615,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f615,plain,(
    ! [X0] :
      ( k2_relat_1(sK3) != X0
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK3))))
      | ~ r1_tarski(k2_relat_1(sK3),X0)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f612,f70])).

fof(f612,plain,(
    ! [X0] :
      ( k2_relat_1(sK3) != X0
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK3))))
      | ~ r1_tarski(k2_relat_1(sK3),X0)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f558,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f558,plain,(
    ! [X10,X11] :
      ( ~ v1_funct_2(sK3,X11,X10)
      | k2_relat_1(sK3) != X10
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X11,X10)))
      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X10,X11))) ) ),
    inference(subsumption_resolution,[],[f555,f70])).

fof(f555,plain,(
    ! [X10,X11] :
      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | k2_relat_1(sK3) != X10
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X11,X10)))
      | ~ v1_funct_2(sK3,X11,X10)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f328,f77])).

fof(f328,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relat_1(X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f327])).

fof(f327,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f110,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

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
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f1963,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3)))) ),
    inference(resolution,[],[f1962,f75])).

fof(f1962,plain,(
    ! [X24,X23] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X23,k2_relat_1(sK3)))) ) ),
    inference(forward_demodulation,[],[f1959,f426])).

fof(f1959,plain,(
    ! [X24,X23] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | m1_subset_1(k5_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(X23,k2_relat_1(sK3)))) ) ),
    inference(resolution,[],[f1950,f73])).

fof(f1950,plain,(
    ! [X6,X7,X5] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | m1_subset_1(k5_relat_1(X5,sK3),k1_zfmisc_1(k2_zfmisc_1(X6,k2_relat_1(sK3)))) ) ),
    inference(resolution,[],[f637,f72])).

fof(f637,plain,(
    ! [X6,X4,X7,X5,X3] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_1(X3)
      | m1_subset_1(k5_relat_1(X3,sK3),k1_zfmisc_1(k2_zfmisc_1(X4,k2_relat_1(sK3)))) ) ),
    inference(resolution,[],[f526,f521])).

fof(f521,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3))))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f508,f136])).

fof(f508,plain,(
    ! [X17,X15,X16] :
      ( ~ r1_tarski(k2_relat_1(sK3),X15)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X15)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) ) ),
    inference(forward_demodulation,[],[f504,f488])).

fof(f504,plain,(
    ! [X17,X15,X16] :
      ( ~ r1_tarski(k2_relat_1(sK3),X15)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X15)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) ) ),
    inference(resolution,[],[f229,f70])).

fof(f229,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ v1_funct_1(X3)
      | ~ r1_tarski(k2_relat_1(X3),X4)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X3),X4)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ) ),
    inference(resolution,[],[f93,f103])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f526,plain,(
    ! [X30,X33,X31,X34,X32] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | m1_subset_1(k5_relat_1(X32,sK3),k1_zfmisc_1(k2_zfmisc_1(X33,X31)))
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | ~ v1_funct_1(X32) ) ),
    inference(resolution,[],[f358,f70])).

fof(f358,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f355])).

fof(f355,plain,(
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
    inference(superposition,[],[f127,f125])).

fof(f4373,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(trivial_inequality_removal,[],[f4371])).

fof(f4371,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relat_1(sK3) != k2_relat_1(sK3)
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f4352,f136])).

fof(f4352,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_relat_1(sK3),X2)
      | k2_relat_1(sK3) != X2
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f4351,f508])).

fof(f4351,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(sK3) != X2
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ r1_tarski(k2_relat_1(sK3),X2) ) ),
    inference(forward_demodulation,[],[f4350,f488])).

fof(f4350,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(sK3) != X2
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X2)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ r1_tarski(k2_relat_1(sK3),X2) ) ),
    inference(subsumption_resolution,[],[f4349,f103])).

fof(f4349,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(sK3) != X2
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X2)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ r1_tarski(k2_relat_1(sK3),X2)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f4346,f70])).

fof(f4346,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(sK3) != X2
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X2)))
      | v1_funct_1(k6_partfun1(sK2))
      | ~ r1_tarski(k2_relat_1(sK3),X2)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f2806,f92])).

fof(f2806,plain,(
    ! [X26,X24,X23,X27,X25,X22] :
      ( ~ v1_funct_2(sK3,X27,X24)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k2_relat_1(sK3) != X24
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24)))
      | v1_funct_1(k6_partfun1(sK2)) ) ),
    inference(forward_demodulation,[],[f2805,f488])).

fof(f2805,plain,(
    ! [X26,X24,X23,X27,X25,X22] :
      ( v1_funct_1(k6_partfun1(k1_relat_1(sK3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k2_relat_1(sK3) != X24
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24)))
      | ~ v1_funct_2(sK3,X27,X24) ) ),
    inference(subsumption_resolution,[],[f2801,f70])).

fof(f2801,plain,(
    ! [X26,X24,X23,X27,X25,X22] :
      ( v1_funct_1(k6_partfun1(k1_relat_1(sK3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | ~ v1_funct_1(sK3)
      | k2_relat_1(sK3) != X24
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24)))
      | ~ v1_funct_2(sK3,X27,X24) ) ),
    inference(resolution,[],[f1474,f77])).

fof(f1474,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ v2_funct_1(X2)
      | v1_funct_1(k6_partfun1(k1_relat_1(X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X2)
      | k2_relat_1(X2) != X1
      | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f1473])).

fof(f1473,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_relat_1(X2) != X1
      | v1_funct_1(k6_partfun1(k1_relat_1(X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f799,f105])).

fof(f799,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_relset_1(X5,X6,X0) != X6
      | v1_funct_1(k6_partfun1(k1_relat_1(X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_2(X0,X5,X6) ) ),
    inference(duplicate_literal_removal,[],[f798])).

fof(f798,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_funct_1(k6_partfun1(k1_relat_1(X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relset_1(X5,X6,X0) != X6
      | ~ v2_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_2(X0,X5,X6)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f518,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f518,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ v1_funct_1(k2_funct_1(X5))
      | ~ m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_funct_1(k6_partfun1(k1_relat_1(X5)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_1(X5)
      | ~ v2_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f515,f103])).

fof(f515,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( v1_funct_1(k6_partfun1(k1_relat_1(X5)))
      | ~ m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_1(k2_funct_1(X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_1(X5)
      | ~ v2_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(duplicate_literal_removal,[],[f513])).

fof(f513,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( v1_funct_1(k6_partfun1(k1_relat_1(X5)))
      | ~ m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_1(k2_funct_1(X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_1(X5)
      | ~ v2_funct_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(superposition,[],[f346,f135])).

fof(f135,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f89,f81])).

fof(f81,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f89,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f346,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k5_relat_1(X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f345])).

fof(f345,plain,(
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
    inference(superposition,[],[f126,f125])).

fof(f126,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f4483,plain,
    ( ~ v1_funct_1(k6_partfun1(sK2))
    | k1_xboole_0 = sK2
    | k6_partfun1(sK2) = sK4 ),
    inference(subsumption_resolution,[],[f4481,f136])).

fof(f4481,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ v1_funct_1(k6_partfun1(sK2))
    | k1_xboole_0 = sK2
    | k6_partfun1(sK2) = sK4 ),
    inference(resolution,[],[f4396,f4272])).

fof(f4272,plain,
    ( ~ v1_funct_2(k6_partfun1(sK2),sK2,sK2)
    | ~ v1_funct_1(k6_partfun1(sK2))
    | k1_xboole_0 = sK2
    | k6_partfun1(sK2) = sK4 ),
    inference(subsumption_resolution,[],[f4271,f72])).

fof(f4271,plain,
    ( ~ v1_funct_2(k6_partfun1(sK2),sK2,sK2)
    | ~ v1_funct_1(k6_partfun1(sK2))
    | k1_xboole_0 = sK2
    | k6_partfun1(sK2) = sK4
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(subsumption_resolution,[],[f4268,f85])).

fof(f85,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f4268,plain,
    ( ~ v1_funct_2(k6_partfun1(sK2),sK2,sK2)
    | ~ v1_funct_1(k6_partfun1(sK2))
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | k6_partfun1(sK2) = sK4
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(resolution,[],[f4267,f317])).

fof(f317,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f316,f85])).

fof(f316,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(duplicate_literal_removal,[],[f313])).

fof(f313,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(superposition,[],[f106,f128])).

fof(f128,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

fof(f4267,plain,(
    ! [X0] :
      ( ~ r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3)
      | ~ v1_funct_2(X0,sK2,sK2)
      | ~ v1_funct_1(X0)
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | sK4 = X0 ) ),
    inference(subsumption_resolution,[],[f4266,f75])).

fof(f4266,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X0,sK2,sK2)
      | ~ v1_funct_1(X0)
      | k1_xboole_0 = sK2
      | ~ r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3)
      | sK4 = X0
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ) ),
    inference(duplicate_literal_removal,[],[f4265])).

fof(f4265,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ v1_funct_2(X0,sK2,sK2)
      | ~ v1_funct_1(X0)
      | k1_xboole_0 = sK2
      | ~ r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3)
      | sK4 = X0
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ) ),
    inference(resolution,[],[f2701,f123])).

fof(f4396,plain,(
    ! [X0] :
      ( v1_funct_2(k6_partfun1(sK2),sK2,X0)
      | ~ r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f4388,f184])).

fof(f184,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(k6_partfun1(X0))
      | v1_funct_2(k6_partfun1(X0),X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f183,f132])).

fof(f132,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f87,f81])).

fof(f87,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f183,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k6_partfun1(X0),X0,X1)
      | ~ r1_tarski(k2_relat_1(k6_partfun1(X0)),X1)
      | ~ v1_funct_1(k6_partfun1(X0)) ) ),
    inference(subsumption_resolution,[],[f181,f131])).

fof(f131,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f82,f81])).

fof(f82,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f181,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k6_partfun1(X0),X0,X1)
      | ~ r1_tarski(k2_relat_1(k6_partfun1(X0)),X1)
      | ~ v1_funct_1(k6_partfun1(X0))
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(superposition,[],[f92,f133])).

fof(f133,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f86,f81])).

fof(f86,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f78,plain,(
    ~ r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f56])).

fof(f5238,plain,(
    sK3 = k2_zfmisc_1(sK2,sK2) ),
    inference(subsumption_resolution,[],[f5237,f80])).

fof(f80,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f5237,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | sK3 = k2_zfmisc_1(sK2,sK2) ),
    inference(forward_demodulation,[],[f4694,f138])).

fof(f4694,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK3)
    | sK3 = k2_zfmisc_1(sK2,sK2) ),
    inference(backward_demodulation,[],[f202,f4688])).

fof(f202,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,sK2),sK3)
    | sK3 = k2_zfmisc_1(sK2,sK2) ),
    inference(resolution,[],[f155,f72])).

fof(f155,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ r1_tarski(X2,X3)
      | X2 = X3 ) ),
    inference(resolution,[],[f97,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
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

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f70,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f5301,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f1313,f5240])).

fof(f1313,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK3) ),
    inference(resolution,[],[f1307,f150])).

fof(f150,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f147,f138])).

fof(f147,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[],[f85,f129])).

fof(f129,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f79,f81])).

fof(f79,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f1307,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_1(X0)
      | k1_xboole_0 = k5_relat_1(X0,sK3) ) ),
    inference(forward_demodulation,[],[f1306,f139])).

fof(f139,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f1306,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k5_relat_1(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f1303,f80])).

fof(f1303,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,k5_relat_1(X0,sK3))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k5_relat_1(X0,sK3) ) ),
    inference(superposition,[],[f644,f139])).

fof(f644,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(k2_zfmisc_1(X7,sK2),k5_relat_1(X6,sK3))
      | ~ v1_funct_1(X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | k2_zfmisc_1(X7,sK2) = k5_relat_1(X6,sK3) ) ),
    inference(resolution,[],[f636,f155])).

fof(f636,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k5_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f526,f72])).

fof(f445,plain,(
    ! [X0] : r2_relset_1(k1_xboole_0,X0,k5_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f413,f150])).

fof(f413,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | r2_relset_1(k1_xboole_0,X0,k5_relat_1(k1_xboole_0,X1),X1) ) ),
    inference(forward_demodulation,[],[f410,f139])).

fof(f410,plain,(
    ! [X0,X1] :
      ( r2_relset_1(k1_xboole_0,X0,k5_relat_1(k1_xboole_0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(superposition,[],[f317,f129])).

fof(f6030,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f5236,f5881])).

fof(f5881,plain,(
    k1_xboole_0 = sK4 ),
    inference(forward_demodulation,[],[f5880,f138])).

fof(f5880,plain,(
    sK4 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f5879,f4688])).

fof(f5879,plain,(
    k2_zfmisc_1(sK2,sK2) = sK4 ),
    inference(subsumption_resolution,[],[f5878,f80])).

fof(f5878,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4)
    | k2_zfmisc_1(sK2,sK2) = sK4 ),
    inference(forward_demodulation,[],[f4695,f138])).

fof(f4695,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK4)
    | k2_zfmisc_1(sK2,sK2) = sK4 ),
    inference(backward_demodulation,[],[f203,f4688])).

fof(f203,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,sK2),sK4)
    | k2_zfmisc_1(sK2,sK2) = sK4 ),
    inference(resolution,[],[f155,f75])).

fof(f5236,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k1_xboole_0) ),
    inference(forward_demodulation,[],[f4693,f129])).

fof(f4693,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k6_partfun1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f78,f4688])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n004.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:45:53 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (7818)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.52  % (7803)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (7811)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (7813)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (7805)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (7802)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (7806)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (7817)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (7807)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (7812)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (7826)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (7804)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.55  % (7830)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (7827)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (7820)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (7810)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (7829)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.56  % (7822)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.56  % (7828)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.56  % (7819)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.56  % (7814)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (7817)Refutation not found, incomplete strategy% (7817)------------------------------
% 0.22/0.56  % (7817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (7817)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (7817)Memory used [KB]: 10746
% 0.22/0.56  % (7817)Time elapsed: 0.148 s
% 0.22/0.56  % (7817)------------------------------
% 0.22/0.56  % (7817)------------------------------
% 0.22/0.56  % (7821)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.57  % (7825)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.57  % (7801)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.58  % (7824)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.58  % (7809)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.58  % (7823)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.59  % (7815)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.59  % (7816)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.60  % (7808)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 2.65/0.74  % (7852)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.03/0.82  % (7825)Time limit reached!
% 3.03/0.82  % (7825)------------------------------
% 3.03/0.82  % (7825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.03/0.82  % (7825)Termination reason: Time limit
% 3.03/0.82  % (7825)Termination phase: Saturation
% 3.03/0.82  
% 3.03/0.82  % (7825)Memory used [KB]: 12665
% 3.03/0.82  % (7825)Time elapsed: 0.400 s
% 3.03/0.82  % (7825)------------------------------
% 3.03/0.82  % (7825)------------------------------
% 3.03/0.83  % (7803)Time limit reached!
% 3.03/0.83  % (7803)------------------------------
% 3.03/0.83  % (7803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.03/0.83  % (7803)Termination reason: Time limit
% 3.03/0.83  
% 3.03/0.83  % (7803)Memory used [KB]: 7036
% 3.03/0.83  % (7803)Time elapsed: 0.412 s
% 3.03/0.83  % (7803)------------------------------
% 3.03/0.83  % (7803)------------------------------
% 4.00/0.91  % (7807)Time limit reached!
% 4.00/0.91  % (7807)------------------------------
% 4.00/0.91  % (7807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.00/0.91  % (7807)Termination reason: Time limit
% 4.00/0.91  % (7807)Termination phase: Saturation
% 4.00/0.91  
% 4.00/0.91  % (7807)Memory used [KB]: 14328
% 4.00/0.91  % (7807)Time elapsed: 0.500 s
% 4.00/0.91  % (7807)------------------------------
% 4.00/0.91  % (7807)------------------------------
% 4.00/0.92  % (7830)Time limit reached!
% 4.00/0.92  % (7830)------------------------------
% 4.00/0.92  % (7830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.00/0.92  % (7830)Termination reason: Time limit
% 4.00/0.92  
% 4.00/0.92  % (7830)Memory used [KB]: 3837
% 4.00/0.92  % (7830)Time elapsed: 0.507 s
% 4.00/0.92  % (7830)------------------------------
% 4.00/0.92  % (7830)------------------------------
% 4.55/0.97  % (7854)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.55/0.98  % (7853)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 4.55/1.00  % (7815)Time limit reached!
% 4.55/1.00  % (7815)------------------------------
% 4.55/1.00  % (7815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.55/1.00  % (7815)Termination reason: Time limit
% 4.55/1.00  % (7815)Termination phase: Saturation
% 4.55/1.00  
% 4.55/1.00  % (7815)Memory used [KB]: 5884
% 4.55/1.00  % (7815)Time elapsed: 0.500 s
% 4.55/1.00  % (7815)------------------------------
% 4.55/1.00  % (7815)------------------------------
% 5.23/1.06  % (7855)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 5.23/1.07  % (7856)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 5.23/1.09  % (7829)Refutation not found, incomplete strategy% (7829)------------------------------
% 5.23/1.09  % (7829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.23/1.09  % (7829)Termination reason: Refutation not found, incomplete strategy
% 5.23/1.09  
% 5.23/1.09  % (7829)Memory used [KB]: 13816
% 5.23/1.09  % (7829)Time elapsed: 0.680 s
% 5.23/1.09  % (7829)------------------------------
% 5.23/1.09  % (7829)------------------------------
% 5.23/1.10  % (7808)Time limit reached!
% 5.23/1.10  % (7808)------------------------------
% 5.23/1.10  % (7808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.23/1.10  % (7808)Termination reason: Time limit
% 5.23/1.10  % (7808)Termination phase: Saturation
% 5.23/1.10  
% 5.23/1.10  % (7808)Memory used [KB]: 6268
% 5.23/1.10  % (7808)Time elapsed: 0.600 s
% 5.23/1.10  % (7808)------------------------------
% 5.23/1.10  % (7808)------------------------------
% 5.23/1.12  % (7857)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 6.48/1.22  % (7802)Time limit reached!
% 6.48/1.22  % (7802)------------------------------
% 6.48/1.22  % (7802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.48/1.22  % (7802)Termination reason: Time limit
% 6.48/1.22  % (7802)Termination phase: Saturation
% 6.48/1.22  
% 6.48/1.22  % (7802)Memory used [KB]: 5884
% 6.48/1.22  % (7802)Time elapsed: 0.800 s
% 6.48/1.22  % (7802)------------------------------
% 6.48/1.22  % (7802)------------------------------
% 6.48/1.22  % (7859)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 6.48/1.23  % (7858)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 7.37/1.34  % (7804)Time limit reached!
% 7.37/1.34  % (7804)------------------------------
% 7.37/1.34  % (7804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.37/1.34  % (7804)Termination reason: Time limit
% 7.37/1.34  
% 7.37/1.34  % (7804)Memory used [KB]: 7931
% 7.37/1.34  % (7804)Time elapsed: 0.926 s
% 7.37/1.34  % (7804)------------------------------
% 7.37/1.34  % (7804)------------------------------
% 7.69/1.36  % (7860)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 7.69/1.41  % (7828)Time limit reached!
% 7.69/1.41  % (7828)------------------------------
% 7.69/1.41  % (7828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.69/1.41  % (7828)Termination reason: Time limit
% 7.69/1.41  % (7828)Termination phase: Saturation
% 7.69/1.41  
% 7.69/1.41  % (7828)Memory used [KB]: 11769
% 7.69/1.41  % (7828)Time elapsed: 1.0000 s
% 7.69/1.41  % (7828)------------------------------
% 7.69/1.41  % (7828)------------------------------
% 8.39/1.45  % (7813)Time limit reached!
% 8.39/1.45  % (7813)------------------------------
% 8.39/1.45  % (7813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.39/1.45  % (7813)Termination reason: Time limit
% 8.39/1.45  
% 8.39/1.45  % (7813)Memory used [KB]: 13944
% 8.39/1.45  % (7813)Time elapsed: 1.047 s
% 8.39/1.45  % (7813)------------------------------
% 8.39/1.45  % (7813)------------------------------
% 8.74/1.53  % (7861)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 9.17/1.56  % (7862)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 9.17/1.60  % (7863)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 9.49/1.66  % (7801)Time limit reached!
% 9.49/1.66  % (7801)------------------------------
% 9.49/1.66  % (7801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.49/1.66  % (7801)Termination reason: Time limit
% 9.49/1.66  
% 9.49/1.66  % (7801)Memory used [KB]: 4093
% 9.49/1.66  % (7801)Time elapsed: 1.227 s
% 9.49/1.66  % (7801)------------------------------
% 9.49/1.66  % (7801)------------------------------
% 10.15/1.68  % (7854)Time limit reached!
% 10.15/1.68  % (7854)------------------------------
% 10.15/1.68  % (7854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.15/1.68  % (7854)Termination reason: Time limit
% 10.15/1.68  
% 10.15/1.68  % (7854)Memory used [KB]: 13304
% 10.15/1.68  % (7854)Time elapsed: 0.821 s
% 10.15/1.68  % (7854)------------------------------
% 10.15/1.68  % (7854)------------------------------
% 10.15/1.72  % (7806)Time limit reached!
% 10.15/1.72  % (7806)------------------------------
% 10.15/1.72  % (7806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.15/1.72  % (7806)Termination reason: Time limit
% 10.15/1.72  
% 10.15/1.72  % (7806)Memory used [KB]: 8571
% 10.15/1.72  % (7806)Time elapsed: 1.309 s
% 10.15/1.72  % (7806)------------------------------
% 10.15/1.72  % (7806)------------------------------
% 10.15/1.73  % (7858)Time limit reached!
% 10.15/1.73  % (7858)------------------------------
% 10.15/1.73  % (7858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.15/1.73  % (7858)Termination reason: Time limit
% 10.15/1.73  % (7858)Termination phase: Saturation
% 10.15/1.73  
% 10.15/1.73  % (7858)Memory used [KB]: 16630
% 10.15/1.73  % (7858)Time elapsed: 0.600 s
% 10.15/1.73  % (7858)------------------------------
% 10.15/1.73  % (7858)------------------------------
% 11.32/1.84  % (7865)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 11.32/1.84  % (7864)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 11.63/1.87  % (7866)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 11.63/1.88  % (7867)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 12.65/2.04  % (7827)Time limit reached!
% 12.65/2.04  % (7827)------------------------------
% 12.65/2.04  % (7827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.65/2.04  % (7827)Termination reason: Time limit
% 12.65/2.04  
% 12.65/2.04  % (7827)Memory used [KB]: 14072
% 12.65/2.04  % (7827)Time elapsed: 1.628 s
% 12.65/2.04  % (7827)------------------------------
% 12.65/2.04  % (7827)------------------------------
% 13.68/2.16  % (7865)Time limit reached!
% 13.68/2.16  % (7865)------------------------------
% 13.68/2.16  % (7865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.68/2.16  % (7865)Termination reason: Time limit
% 13.68/2.16  
% 13.68/2.16  % (7865)Memory used [KB]: 14200
% 13.68/2.16  % (7865)Time elapsed: 0.417 s
% 13.68/2.16  % (7865)------------------------------
% 13.68/2.16  % (7865)------------------------------
% 13.68/2.19  % (7861)Time limit reached!
% 13.68/2.19  % (7861)------------------------------
% 13.68/2.19  % (7861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.68/2.19  % (7861)Termination reason: Time limit
% 13.68/2.19  % (7861)Termination phase: Saturation
% 13.68/2.19  
% 13.68/2.19  % (7861)Memory used [KB]: 14967
% 13.68/2.19  % (7861)Time elapsed: 0.800 s
% 13.68/2.19  % (7861)------------------------------
% 13.68/2.19  % (7861)------------------------------
% 13.68/2.19  % (7867)Time limit reached!
% 13.68/2.19  % (7867)------------------------------
% 13.68/2.19  % (7867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.68/2.19  % (7867)Termination reason: Time limit
% 13.68/2.19  % (7867)Termination phase: Saturation
% 13.68/2.19  
% 13.68/2.19  % (7867)Memory used [KB]: 7036
% 13.68/2.19  % (7867)Time elapsed: 0.413 s
% 13.68/2.19  % (7867)------------------------------
% 13.68/2.19  % (7867)------------------------------
% 13.68/2.19  % (7868)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 13.68/2.20  % (7823)Refutation found. Thanks to Tanya!
% 13.68/2.20  % SZS status Theorem for theBenchmark
% 13.68/2.20  % SZS output start Proof for theBenchmark
% 13.68/2.20  fof(f6283,plain,(
% 13.68/2.20    $false),
% 13.68/2.20    inference(subsumption_resolution,[],[f6030,f5528])).
% 13.68/2.20  fof(f5528,plain,(
% 13.68/2.20    ( ! [X0] : (r2_relset_1(k1_xboole_0,X0,k1_xboole_0,k1_xboole_0)) )),
% 13.68/2.20    inference(backward_demodulation,[],[f445,f5525])).
% 13.68/2.20  fof(f5525,plain,(
% 13.68/2.20    k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0)),
% 13.68/2.20    inference(subsumption_resolution,[],[f5301,f5241])).
% 13.68/2.20  fof(f5241,plain,(
% 13.68/2.20    v1_funct_1(k1_xboole_0)),
% 13.68/2.20    inference(backward_demodulation,[],[f70,f5240])).
% 13.68/2.20  fof(f5240,plain,(
% 13.68/2.20    k1_xboole_0 = sK3),
% 13.68/2.20    inference(forward_demodulation,[],[f5239,f138])).
% 13.68/2.20  fof(f138,plain,(
% 13.68/2.20    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 13.68/2.20    inference(equality_resolution,[],[f102])).
% 13.68/2.20  fof(f102,plain,(
% 13.68/2.20    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 13.68/2.20    inference(cnf_transformation,[],[f61])).
% 13.68/2.20  fof(f61,plain,(
% 13.68/2.20    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 13.68/2.20    inference(flattening,[],[f60])).
% 13.68/2.20  fof(f60,plain,(
% 13.68/2.20    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 13.68/2.20    inference(nnf_transformation,[],[f3])).
% 13.68/2.20  fof(f3,axiom,(
% 13.68/2.20    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 13.68/2.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 13.68/2.20  fof(f5239,plain,(
% 13.68/2.20    sK3 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),
% 13.68/2.20    inference(forward_demodulation,[],[f5238,f4688])).
% 13.68/2.20  fof(f4688,plain,(
% 13.68/2.20    k1_xboole_0 = sK2),
% 13.68/2.20    inference(subsumption_resolution,[],[f4687,f406])).
% 13.68/2.20  fof(f406,plain,(
% 13.68/2.20    r2_relset_1(sK2,sK2,sK3,sK3)),
% 13.68/2.20    inference(backward_demodulation,[],[f76,f404])).
% 13.68/2.20  fof(f404,plain,(
% 13.68/2.20    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 13.68/2.20    inference(subsumption_resolution,[],[f403,f73])).
% 13.68/2.20  fof(f73,plain,(
% 13.68/2.20    v1_funct_1(sK4)),
% 13.68/2.20    inference(cnf_transformation,[],[f56])).
% 13.68/2.20  fof(f56,plain,(
% 13.68/2.20    (~r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 13.68/2.20    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f27,f55,f54])).
% 13.68/2.20  fof(f54,plain,(
% 13.68/2.20    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK2,sK2,X2,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X2,sK3),sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(X2,sK2,sK2) & v1_funct_1(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 13.68/2.20    introduced(choice_axiom,[])).
% 13.68/2.20  fof(f55,plain,(
% 13.68/2.20    ? [X2] : (~r2_relset_1(sK2,sK2,X2,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,X2,sK3),sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(X2,sK2,sK2) & v1_funct_1(X2)) => (~r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2)) & v2_funct_1(sK3) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4))),
% 13.68/2.20    introduced(choice_axiom,[])).
% 13.68/2.20  fof(f27,plain,(
% 13.68/2.20    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 13.68/2.20    inference(flattening,[],[f26])).
% 13.68/2.20  fof(f26,plain,(
% 13.68/2.20    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 13.68/2.20    inference(ennf_transformation,[],[f25])).
% 13.68/2.20  fof(f25,negated_conjecture,(
% 13.68/2.20    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 13.68/2.20    inference(negated_conjecture,[],[f24])).
% 13.68/2.20  fof(f24,conjecture,(
% 13.68/2.20    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 13.68/2.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_funct_2)).
% 13.68/2.20  fof(f403,plain,(
% 13.68/2.20    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) | ~v1_funct_1(sK4)),
% 13.68/2.20    inference(subsumption_resolution,[],[f402,f75])).
% 13.68/2.20  fof(f75,plain,(
% 13.68/2.20    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 13.68/2.20    inference(cnf_transformation,[],[f56])).
% 13.68/2.20  fof(f402,plain,(
% 13.68/2.20    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4)),
% 13.68/2.20    inference(subsumption_resolution,[],[f401,f70])).
% 13.68/2.20  fof(f401,plain,(
% 13.68/2.20    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4)),
% 13.68/2.20    inference(subsumption_resolution,[],[f398,f72])).
% 13.68/2.20  fof(f72,plain,(
% 13.68/2.20    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 13.68/2.20    inference(cnf_transformation,[],[f56])).
% 13.68/2.20  fof(f398,plain,(
% 13.68/2.20    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4)),
% 13.68/2.20    inference(resolution,[],[f294,f127])).
% 13.68/2.20  fof(f127,plain,(
% 13.68/2.20    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 13.68/2.20    inference(cnf_transformation,[],[f48])).
% 13.68/2.20  fof(f48,plain,(
% 13.68/2.20    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 13.68/2.20    inference(flattening,[],[f47])).
% 13.68/2.20  fof(f47,plain,(
% 13.68/2.20    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 13.68/2.20    inference(ennf_transformation,[],[f15])).
% 13.68/2.20  fof(f15,axiom,(
% 13.68/2.20    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 13.68/2.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 13.68/2.20  fof(f294,plain,(
% 13.68/2.20    ~m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3)),
% 13.68/2.20    inference(subsumption_resolution,[],[f287,f72])).
% 13.68/2.20  fof(f287,plain,(
% 13.68/2.20    sK3 = k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~m1_subset_1(k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 13.68/2.20    inference(resolution,[],[f123,f76])).
% 13.68/2.20  fof(f123,plain,(
% 13.68/2.20    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 13.68/2.20    inference(cnf_transformation,[],[f69])).
% 13.68/2.20  fof(f69,plain,(
% 13.68/2.20    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 13.68/2.20    inference(nnf_transformation,[],[f44])).
% 13.68/2.20  fof(f44,plain,(
% 13.68/2.20    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 13.68/2.20    inference(flattening,[],[f43])).
% 13.68/2.20  fof(f43,plain,(
% 13.68/2.20    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 13.68/2.20    inference(ennf_transformation,[],[f14])).
% 13.68/2.20  fof(f14,axiom,(
% 13.68/2.20    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 13.68/2.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 13.68/2.20  fof(f76,plain,(
% 13.68/2.20    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK4,sK3),sK3)),
% 13.68/2.20    inference(cnf_transformation,[],[f56])).
% 13.68/2.20  fof(f4687,plain,(
% 13.68/2.20    ~r2_relset_1(sK2,sK2,sK3,sK3) | k1_xboole_0 = sK2),
% 13.68/2.20    inference(forward_demodulation,[],[f4686,f426])).
% 13.68/2.20  fof(f426,plain,(
% 13.68/2.20    sK3 = k5_relat_1(sK4,sK3)),
% 13.68/2.20    inference(subsumption_resolution,[],[f425,f73])).
% 13.68/2.20  fof(f425,plain,(
% 13.68/2.20    sK3 = k5_relat_1(sK4,sK3) | ~v1_funct_1(sK4)),
% 13.68/2.20    inference(subsumption_resolution,[],[f424,f75])).
% 13.68/2.20  fof(f424,plain,(
% 13.68/2.20    sK3 = k5_relat_1(sK4,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4)),
% 13.68/2.20    inference(subsumption_resolution,[],[f423,f70])).
% 13.68/2.20  fof(f423,plain,(
% 13.68/2.20    sK3 = k5_relat_1(sK4,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4)),
% 13.68/2.20    inference(subsumption_resolution,[],[f417,f72])).
% 13.68/2.20  fof(f417,plain,(
% 13.68/2.20    sK3 = k5_relat_1(sK4,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4)),
% 13.68/2.20    inference(superposition,[],[f404,f125])).
% 13.68/2.20  fof(f125,plain,(
% 13.68/2.20    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 13.68/2.20    inference(cnf_transformation,[],[f46])).
% 13.68/2.20  fof(f46,plain,(
% 13.68/2.20    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 13.68/2.20    inference(flattening,[],[f45])).
% 13.68/2.20  fof(f45,plain,(
% 13.68/2.20    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 13.68/2.20    inference(ennf_transformation,[],[f17])).
% 13.68/2.20  fof(f17,axiom,(
% 13.68/2.20    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 13.68/2.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 13.68/2.20  fof(f4686,plain,(
% 13.68/2.20    k1_xboole_0 = sK2 | ~r2_relset_1(sK2,sK2,k5_relat_1(sK4,sK3),sK3)),
% 13.68/2.20    inference(subsumption_resolution,[],[f4685,f73])).
% 13.68/2.20  fof(f4685,plain,(
% 13.68/2.20    k1_xboole_0 = sK2 | ~v1_funct_1(sK4) | ~r2_relset_1(sK2,sK2,k5_relat_1(sK4,sK3),sK3)),
% 13.68/2.20    inference(subsumption_resolution,[],[f4684,f74])).
% 13.68/2.20  fof(f74,plain,(
% 13.68/2.20    v1_funct_2(sK4,sK2,sK2)),
% 13.68/2.20    inference(cnf_transformation,[],[f56])).
% 13.68/2.20  fof(f4684,plain,(
% 13.68/2.20    k1_xboole_0 = sK2 | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4) | ~r2_relset_1(sK2,sK2,k5_relat_1(sK4,sK3),sK3)),
% 13.68/2.20    inference(subsumption_resolution,[],[f4683,f75])).
% 13.68/2.20  fof(f4683,plain,(
% 13.68/2.20    k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4) | ~r2_relset_1(sK2,sK2,k5_relat_1(sK4,sK3),sK3)),
% 13.68/2.20    inference(duplicate_literal_removal,[],[f4680])).
% 13.68/2.20  fof(f4680,plain,(
% 13.68/2.20    k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(sK4,sK2,sK2) | ~v1_funct_1(sK4) | k1_xboole_0 = sK2 | ~r2_relset_1(sK2,sK2,k5_relat_1(sK4,sK3),sK3)),
% 13.68/2.20    inference(resolution,[],[f4493,f2701])).
% 13.68/2.20  fof(f2701,plain,(
% 13.68/2.20    ( ! [X3] : (r2_relset_1(sK2,sK2,X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X3,sK2,sK2) | ~v1_funct_1(X3) | k1_xboole_0 = sK2 | ~r2_relset_1(sK2,sK2,k5_relat_1(X3,sK3),sK3)) )),
% 13.68/2.20    inference(subsumption_resolution,[],[f2700,f75])).
% 13.68/2.20  fof(f2700,plain,(
% 13.68/2.20    ( ! [X3] : (~r2_relset_1(sK2,sK2,k5_relat_1(X3,sK3),sK3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X3,sK2,sK2) | ~v1_funct_1(X3) | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | r2_relset_1(sK2,sK2,X3,sK4)) )),
% 13.68/2.20    inference(subsumption_resolution,[],[f2699,f74])).
% 13.68/2.20  fof(f2699,plain,(
% 13.68/2.20    ( ! [X3] : (~r2_relset_1(sK2,sK2,k5_relat_1(X3,sK3),sK3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X3,sK2,sK2) | ~v1_funct_1(X3) | ~v1_funct_2(sK4,sK2,sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | r2_relset_1(sK2,sK2,X3,sK4)) )),
% 13.68/2.20    inference(subsumption_resolution,[],[f2694,f73])).
% 13.68/2.20  fof(f2694,plain,(
% 13.68/2.20    ( ! [X3] : (~r2_relset_1(sK2,sK2,k5_relat_1(X3,sK3),sK3) | ~v1_funct_1(sK4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X3,sK2,sK2) | ~v1_funct_1(X3) | ~v1_funct_2(sK4,sK2,sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | r2_relset_1(sK2,sK2,X3,sK4)) )),
% 13.68/2.20    inference(superposition,[],[f1529,f404])).
% 13.68/2.20  fof(f1529,plain,(
% 13.68/2.20    ( ! [X6,X4,X5] : (~r2_relset_1(X5,sK2,k5_relat_1(X6,sK3),k1_partfun1(X5,sK2,sK2,sK2,X4,sK3)) | ~v1_funct_1(X4) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,sK2))) | ~v1_funct_2(X6,X5,sK2) | ~v1_funct_1(X6) | ~v1_funct_2(X4,X5,sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,sK2))) | r2_relset_1(X5,sK2,X6,X4)) )),
% 13.68/2.20    inference(subsumption_resolution,[],[f1518,f72])).
% 13.68/2.20  fof(f1518,plain,(
% 13.68/2.20    ( ! [X6,X4,X5] : (~v1_funct_2(X4,X5,sK2) | ~v1_funct_1(X4) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,sK2))) | ~v1_funct_2(X6,X5,sK2) | ~v1_funct_1(X6) | ~r2_relset_1(X5,sK2,k5_relat_1(X6,sK3),k1_partfun1(X5,sK2,sK2,sK2,X4,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | k1_xboole_0 = sK2 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,sK2))) | r2_relset_1(X5,sK2,X6,X4)) )),
% 13.68/2.20    inference(duplicate_literal_removal,[],[f1516])).
% 13.68/2.20  fof(f1516,plain,(
% 13.68/2.20    ( ! [X6,X4,X5] : (~v1_funct_2(X4,X5,sK2) | ~v1_funct_1(X4) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,sK2))) | ~v1_funct_2(X6,X5,sK2) | ~v1_funct_1(X6) | ~r2_relset_1(X5,sK2,k5_relat_1(X6,sK3),k1_partfun1(X5,sK2,sK2,sK2,X4,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | k1_xboole_0 = sK2 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,sK2))) | r2_relset_1(X5,sK2,X6,X4) | k1_xboole_0 = sK2) )),
% 13.68/2.20    inference(resolution,[],[f1033,f71])).
% 13.68/2.20  fof(f71,plain,(
% 13.68/2.20    v1_funct_2(sK3,sK2,sK2)),
% 13.68/2.20    inference(cnf_transformation,[],[f56])).
% 13.68/2.20  fof(f1033,plain,(
% 13.68/2.20    ( ! [X23,X21,X19,X22,X20] : (~v1_funct_2(sK3,X21,X23) | ~v1_funct_2(X19,X20,X21) | ~v1_funct_1(X19) | ~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) | ~v1_funct_2(X22,X20,X21) | ~v1_funct_1(X22) | ~r2_relset_1(X20,X23,k5_relat_1(X22,sK3),k1_partfun1(X20,X21,X21,X23,X19,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X21,X23))) | k1_xboole_0 = X21 | ~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) | r2_relset_1(X20,X21,X22,X19) | k1_xboole_0 = X23) )),
% 13.68/2.20    inference(subsumption_resolution,[],[f1032,f70])).
% 13.68/2.20  fof(f1032,plain,(
% 13.68/2.20    ( ! [X23,X21,X19,X22,X20] : (~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) | ~v1_funct_2(X19,X20,X21) | ~v1_funct_1(X19) | ~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) | ~v1_funct_2(X22,X20,X21) | ~v1_funct_1(X22) | ~r2_relset_1(X20,X23,k5_relat_1(X22,sK3),k1_partfun1(X20,X21,X21,X23,X19,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X21,X23))) | ~v1_funct_1(sK3) | k1_xboole_0 = X21 | ~v1_funct_2(sK3,X21,X23) | r2_relset_1(X20,X21,X22,X19) | k1_xboole_0 = X23) )),
% 13.68/2.20    inference(resolution,[],[f611,f77])).
% 13.68/2.20  fof(f77,plain,(
% 13.68/2.20    v2_funct_1(sK3)),
% 13.68/2.20    inference(cnf_transformation,[],[f56])).
% 13.68/2.20  fof(f611,plain,(
% 13.68/2.20    ( ! [X4,X2,X0,X5,X3,X1] : (~v2_funct_1(X5) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~r2_relset_1(X0,X4,k5_relat_1(X2,X5),k1_partfun1(X0,X1,X1,X4,X3,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) | ~v1_funct_1(X5) | k1_xboole_0 = X1 | ~v1_funct_2(X5,X1,X4) | r2_relset_1(X0,X1,X2,X3) | k1_xboole_0 = X4) )),
% 13.68/2.20    inference(duplicate_literal_removal,[],[f607])).
% 13.68/2.20  fof(f607,plain,(
% 13.68/2.20    ( ! [X4,X2,X0,X5,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~r2_relset_1(X0,X4,k5_relat_1(X2,X5),k1_partfun1(X0,X1,X1,X4,X3,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) | ~v1_funct_1(X5) | k1_xboole_0 = X1 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) | ~v1_funct_2(X5,X1,X4) | ~v1_funct_1(X5) | ~v2_funct_1(X5) | k1_xboole_0 = X4) )),
% 13.68/2.20    inference(resolution,[],[f377,f307])).
% 13.68/2.20  fof(f307,plain,(
% 13.68/2.20    ( ! [X2,X0,X1] : (sP0(X1,X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X1,X0) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X0) )),
% 13.68/2.20    inference(resolution,[],[f122,f111])).
% 13.68/2.20  fof(f111,plain,(
% 13.68/2.20    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~v2_funct_1(X1) | sP0(X2,X1,X0)) )),
% 13.68/2.20    inference(cnf_transformation,[],[f63])).
% 13.68/2.20  fof(f63,plain,(
% 13.68/2.20    ! [X0,X1,X2] : (((v2_funct_1(X1) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~v2_funct_1(X1))) | ~sP1(X0,X1,X2))),
% 13.68/2.20    inference(rectify,[],[f62])).
% 13.68/2.20  fof(f62,plain,(
% 13.68/2.20    ! [X1,X2,X0] : (((v2_funct_1(X2) | ~sP0(X0,X2,X1)) & (sP0(X0,X2,X1) | ~v2_funct_1(X2))) | ~sP1(X1,X2,X0))),
% 13.68/2.20    inference(nnf_transformation,[],[f52])).
% 13.68/2.20  fof(f52,plain,(
% 13.68/2.20    ! [X1,X2,X0] : ((v2_funct_1(X2) <=> sP0(X0,X2,X1)) | ~sP1(X1,X2,X0))),
% 13.68/2.20    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 13.68/2.20  fof(f122,plain,(
% 13.68/2.20    ( ! [X2,X0,X1] : (sP1(X1,X2,X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 13.68/2.20    inference(cnf_transformation,[],[f53])).
% 13.68/2.20  fof(f53,plain,(
% 13.68/2.20    ! [X0,X1,X2] : (sP1(X1,X2,X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 13.68/2.20    inference(definition_folding,[],[f42,f52,f51])).
% 13.68/2.20  fof(f51,plain,(
% 13.68/2.20    ! [X0,X2,X1] : (sP0(X0,X2,X1) <=> ! [X3,X4] : (! [X5] : (r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4)))),
% 13.68/2.20    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 13.68/2.20  fof(f42,plain,(
% 13.68/2.20    ! [X0,X1,X2] : ((v2_funct_1(X2) <=> ! [X3,X4] : (! [X5] : (r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4))) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 13.68/2.20    inference(flattening,[],[f41])).
% 13.68/2.20  fof(f41,plain,(
% 13.68/2.20    ! [X0,X1,X2] : (((v2_funct_1(X2) <=> ! [X3,X4] : (! [X5] : ((r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4)))) | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 13.68/2.20    inference(ennf_transformation,[],[f20])).
% 13.68/2.20  fof(f20,axiom,(
% 13.68/2.20    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ~(~(v2_funct_1(X2) <=> ! [X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X4,X3,X0) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X5,X3,X0) & v1_funct_1(X5)) => (r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) => r2_relset_1(X3,X0,X4,X5))))) & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 13.68/2.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_2)).
% 13.68/2.20  fof(f377,plain,(
% 13.68/2.20    ( ! [X4,X2,X0,X5,X3,X1] : (~sP0(X1,X4,X2) | r2_relset_1(X0,X1,X3,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r2_relset_1(X0,X2,k5_relat_1(X3,X4),k1_partfun1(X0,X1,X1,X2,X5,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4)) )),
% 13.68/2.20    inference(duplicate_literal_removal,[],[f374])).
% 13.68/2.20  fof(f374,plain,(
% 13.68/2.20    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_relset_1(X0,X2,k5_relat_1(X3,X4),k1_partfun1(X0,X1,X1,X2,X5,X4)) | r2_relset_1(X0,X1,X3,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~sP0(X1,X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) )),
% 13.68/2.20    inference(superposition,[],[f113,f125])).
% 13.68/2.20  fof(f113,plain,(
% 13.68/2.20    ( ! [X6,X2,X0,X8,X7,X1] : (~r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1)) | r2_relset_1(X6,X0,X7,X8) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X8,X6,X0) | ~v1_funct_1(X8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X7,X6,X0) | ~v1_funct_1(X7) | ~sP0(X0,X1,X2)) )),
% 13.68/2.20    inference(cnf_transformation,[],[f68])).
% 13.68/2.20  fof(f68,plain,(
% 13.68/2.20    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK7(X0,X1,X2),X1)) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(sK7(X0,X1,X2),sK5(X0,X1,X2),X0) & v1_funct_1(sK7(X0,X1,X2))) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(sK6(X0,X1,X2),sK5(X0,X1,X2),X0) & v1_funct_1(sK6(X0,X1,X2)))) & (! [X6,X7] : (! [X8] : (r2_relset_1(X6,X0,X7,X8) | ~r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X8,X6,X0) | ~v1_funct_1(X8)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X7,X6,X0) | ~v1_funct_1(X7)) | ~sP0(X0,X1,X2)))),
% 13.68/2.20    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f65,f67,f66])).
% 13.68/2.20  fof(f66,plain,(
% 13.68/2.20    ! [X2,X1,X0] : (? [X3,X4] : (? [X5] : (~r2_relset_1(X3,X0,X4,X5) & r2_relset_1(X3,X2,k1_partfun1(X3,X0,X0,X2,X4,X1),k1_partfun1(X3,X0,X0,X2,X5,X1)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X5,X3,X0) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X4,X3,X0) & v1_funct_1(X4)) => (? [X5] : (~r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),X5) & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,X5,X1)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(X5,sK5(X0,X1,X2),X0) & v1_funct_1(X5)) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(sK6(X0,X1,X2),sK5(X0,X1,X2),X0) & v1_funct_1(sK6(X0,X1,X2))))),
% 13.68/2.20    introduced(choice_axiom,[])).
% 13.68/2.20  fof(f67,plain,(
% 13.68/2.20    ! [X2,X1,X0] : (? [X5] : (~r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),X5) & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,X5,X1)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(X5,sK5(X0,X1,X2),X0) & v1_funct_1(X5)) => (~r2_relset_1(sK5(X0,X1,X2),X0,sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_relset_1(sK5(X0,X1,X2),X2,k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK6(X0,X1,X2),X1),k1_partfun1(sK5(X0,X1,X2),X0,X0,X2,sK7(X0,X1,X2),X1)) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(sK5(X0,X1,X2),X0))) & v1_funct_2(sK7(X0,X1,X2),sK5(X0,X1,X2),X0) & v1_funct_1(sK7(X0,X1,X2))))),
% 13.68/2.20    introduced(choice_axiom,[])).
% 13.68/2.20  fof(f65,plain,(
% 13.68/2.20    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3,X4] : (? [X5] : (~r2_relset_1(X3,X0,X4,X5) & r2_relset_1(X3,X2,k1_partfun1(X3,X0,X0,X2,X4,X1),k1_partfun1(X3,X0,X0,X2,X5,X1)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X5,X3,X0) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X4,X3,X0) & v1_funct_1(X4))) & (! [X6,X7] : (! [X8] : (r2_relset_1(X6,X0,X7,X8) | ~r2_relset_1(X6,X2,k1_partfun1(X6,X0,X0,X2,X7,X1),k1_partfun1(X6,X0,X0,X2,X8,X1)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X8,X6,X0) | ~v1_funct_1(X8)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X0))) | ~v1_funct_2(X7,X6,X0) | ~v1_funct_1(X7)) | ~sP0(X0,X1,X2)))),
% 13.68/2.20    inference(rectify,[],[f64])).
% 13.68/2.20  fof(f64,plain,(
% 13.68/2.20    ! [X0,X2,X1] : ((sP0(X0,X2,X1) | ? [X3,X4] : (? [X5] : (~r2_relset_1(X3,X0,X4,X5) & r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X5,X3,X0) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) & v1_funct_2(X4,X3,X0) & v1_funct_1(X4))) & (! [X3,X4] : (! [X5] : (r2_relset_1(X3,X0,X4,X5) | ~r2_relset_1(X3,X1,k1_partfun1(X3,X0,X0,X1,X4,X2),k1_partfun1(X3,X0,X0,X1,X5,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X5,X3,X0) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4)) | ~sP0(X0,X2,X1)))),
% 13.68/2.20    inference(nnf_transformation,[],[f51])).
% 13.68/2.20  fof(f4493,plain,(
% 13.68/2.20    ~r2_relset_1(sK2,sK2,sK4,sK4) | k1_xboole_0 = sK2),
% 13.68/2.20    inference(superposition,[],[f78,f4484])).
% 13.68/2.20  fof(f4484,plain,(
% 13.68/2.20    k6_partfun1(sK2) = sK4 | k1_xboole_0 = sK2),
% 13.68/2.20    inference(subsumption_resolution,[],[f4483,f4388])).
% 13.68/2.20  fof(f4388,plain,(
% 13.68/2.20    v1_funct_1(k6_partfun1(sK2))),
% 13.68/2.20    inference(resolution,[],[f4374,f72])).
% 13.68/2.20  fof(f4374,plain,(
% 13.68/2.20    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k6_partfun1(sK2))) )),
% 13.68/2.20    inference(resolution,[],[f4373,f1970])).
% 13.68/2.20  fof(f1970,plain,(
% 13.68/2.20    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),sK2)))),
% 13.68/2.20    inference(resolution,[],[f1963,f948])).
% 13.68/2.20  fof(f948,plain,(
% 13.68/2.20    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3)))) | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),sK2)))),
% 13.68/2.20    inference(trivial_inequality_removal,[],[f946])).
% 13.68/2.20  fof(f946,plain,(
% 13.68/2.20    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3)))) | k2_relat_1(sK3) != k2_relat_1(sK3) | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),sK2)))),
% 13.68/2.20    inference(resolution,[],[f618,f136])).
% 13.68/2.20  fof(f136,plain,(
% 13.68/2.20    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 13.68/2.20    inference(equality_resolution,[],[f96])).
% 13.68/2.20  fof(f96,plain,(
% 13.68/2.20    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 13.68/2.20    inference(cnf_transformation,[],[f58])).
% 13.68/2.20  fof(f58,plain,(
% 13.68/2.20    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 13.68/2.20    inference(flattening,[],[f57])).
% 13.68/2.20  fof(f57,plain,(
% 13.68/2.20    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 13.68/2.20    inference(nnf_transformation,[],[f1])).
% 13.68/2.20  fof(f1,axiom,(
% 13.68/2.20    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 13.68/2.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 13.68/2.20  fof(f618,plain,(
% 13.68/2.20    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | k2_relat_1(sK3) != X0 | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) )),
% 13.68/2.20    inference(forward_demodulation,[],[f617,f488])).
% 13.68/2.20  fof(f488,plain,(
% 13.68/2.20    sK2 = k1_relat_1(sK3)),
% 13.68/2.20    inference(subsumption_resolution,[],[f487,f70])).
% 13.68/2.20  fof(f487,plain,(
% 13.68/2.20    sK2 = k1_relat_1(sK3) | ~v1_funct_1(sK3)),
% 13.68/2.20    inference(subsumption_resolution,[],[f482,f72])).
% 13.68/2.20  fof(f482,plain,(
% 13.68/2.20    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | sK2 = k1_relat_1(sK3) | ~v1_funct_1(sK3)),
% 13.68/2.20    inference(resolution,[],[f252,f71])).
% 13.68/2.20  fof(f252,plain,(
% 13.68/2.20    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relat_1(X1) = X0 | ~v1_funct_1(X1)) )),
% 13.68/2.20    inference(duplicate_literal_removal,[],[f249])).
% 13.68/2.20  fof(f249,plain,(
% 13.68/2.20    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 13.68/2.20    inference(superposition,[],[f94,f104])).
% 13.68/2.20  fof(f104,plain,(
% 13.68/2.20    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 13.68/2.20    inference(cnf_transformation,[],[f36])).
% 13.68/2.20  fof(f36,plain,(
% 13.68/2.20    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 13.68/2.20    inference(ennf_transformation,[],[f11])).
% 13.68/2.20  fof(f11,axiom,(
% 13.68/2.20    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 13.68/2.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 13.68/2.20  fof(f94,plain,(
% 13.68/2.20    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 13.68/2.20    inference(cnf_transformation,[],[f34])).
% 13.68/2.20  fof(f34,plain,(
% 13.68/2.20    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 13.68/2.20    inference(flattening,[],[f33])).
% 13.68/2.20  fof(f33,plain,(
% 13.68/2.20    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 13.68/2.20    inference(ennf_transformation,[],[f23])).
% 13.68/2.20  fof(f23,axiom,(
% 13.68/2.20    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 13.68/2.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).
% 13.68/2.20  fof(f617,plain,(
% 13.68/2.20    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | k2_relat_1(sK3) != X0 | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK3)))) | ~r1_tarski(k2_relat_1(sK3),X0)) )),
% 13.68/2.20    inference(forward_demodulation,[],[f616,f488])).
% 13.68/2.20  fof(f616,plain,(
% 13.68/2.20    ( ! [X0] : (k2_relat_1(sK3) != X0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK3)))) | ~r1_tarski(k2_relat_1(sK3),X0)) )),
% 13.68/2.20    inference(subsumption_resolution,[],[f615,f103])).
% 13.68/2.20  fof(f103,plain,(
% 13.68/2.20    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 13.68/2.20    inference(cnf_transformation,[],[f35])).
% 13.68/2.20  fof(f35,plain,(
% 13.68/2.20    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 13.68/2.20    inference(ennf_transformation,[],[f10])).
% 13.68/2.20  fof(f10,axiom,(
% 13.68/2.20    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 13.68/2.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 13.68/2.20  fof(f615,plain,(
% 13.68/2.20    ( ! [X0] : (k2_relat_1(sK3) != X0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK3)))) | ~r1_tarski(k2_relat_1(sK3),X0) | ~v1_relat_1(sK3)) )),
% 13.68/2.20    inference(subsumption_resolution,[],[f612,f70])).
% 13.68/2.20  fof(f612,plain,(
% 13.68/2.20    ( ! [X0] : (k2_relat_1(sK3) != X0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK3)))) | ~r1_tarski(k2_relat_1(sK3),X0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 13.68/2.20    inference(resolution,[],[f558,f92])).
% 13.68/2.20  fof(f92,plain,(
% 13.68/2.20    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 13.68/2.20    inference(cnf_transformation,[],[f32])).
% 13.68/2.20  fof(f32,plain,(
% 13.68/2.20    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 13.68/2.20    inference(flattening,[],[f31])).
% 13.68/2.20  fof(f31,plain,(
% 13.68/2.20    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 13.68/2.20    inference(ennf_transformation,[],[f22])).
% 13.68/2.20  fof(f22,axiom,(
% 13.68/2.20    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 13.68/2.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 13.68/2.20  fof(f558,plain,(
% 13.68/2.20    ( ! [X10,X11] : (~v1_funct_2(sK3,X11,X10) | k2_relat_1(sK3) != X10 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X11,X10))) | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) )),
% 13.68/2.20    inference(subsumption_resolution,[],[f555,f70])).
% 13.68/2.20  fof(f555,plain,(
% 13.68/2.20    ( ! [X10,X11] : (m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | k2_relat_1(sK3) != X10 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X11,X10))) | ~v1_funct_2(sK3,X11,X10) | ~v1_funct_1(sK3)) )),
% 13.68/2.20    inference(resolution,[],[f328,f77])).
% 13.68/2.20  fof(f328,plain,(
% 13.68/2.20    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relat_1(X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 13.68/2.20    inference(duplicate_literal_removal,[],[f327])).
% 13.68/2.20  fof(f327,plain,(
% 13.68/2.20    ( ! [X2,X0,X1] : (k2_relat_1(X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 13.68/2.20    inference(superposition,[],[f110,f105])).
% 13.68/2.20  fof(f105,plain,(
% 13.68/2.20    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 13.68/2.20    inference(cnf_transformation,[],[f37])).
% 13.68/2.20  fof(f37,plain,(
% 13.68/2.20    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 13.68/2.20    inference(ennf_transformation,[],[f12])).
% 13.68/2.20  fof(f12,axiom,(
% 13.68/2.20    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 13.68/2.20    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 13.68/2.20  fof(f110,plain,(
% 13.68/2.20    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 13.68/2.20    inference(cnf_transformation,[],[f40])).
% 13.68/2.20  fof(f40,plain,(
% 13.68/2.20    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 13.68/2.20    inference(flattening,[],[f39])).
% 13.68/2.20  fof(f39,plain,(
% 13.68/2.20    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 13.68/2.20    inference(ennf_transformation,[],[f21])).
% 13.68/2.22  fof(f21,axiom,(
% 13.68/2.22    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 13.68/2.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 13.68/2.22  fof(f1963,plain,(
% 13.68/2.22    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3))))),
% 13.68/2.22    inference(resolution,[],[f1962,f75])).
% 13.68/2.22  fof(f1962,plain,(
% 13.68/2.22    ( ! [X24,X23] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X23,k2_relat_1(sK3))))) )),
% 13.68/2.22    inference(forward_demodulation,[],[f1959,f426])).
% 13.68/2.22  fof(f1959,plain,(
% 13.68/2.22    ( ! [X24,X23] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) | m1_subset_1(k5_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(X23,k2_relat_1(sK3))))) )),
% 13.68/2.22    inference(resolution,[],[f1950,f73])).
% 13.68/2.22  fof(f1950,plain,(
% 13.68/2.22    ( ! [X6,X7,X5] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | m1_subset_1(k5_relat_1(X5,sK3),k1_zfmisc_1(k2_zfmisc_1(X6,k2_relat_1(sK3))))) )),
% 13.68/2.22    inference(resolution,[],[f637,f72])).
% 13.68/2.22  fof(f637,plain,(
% 13.68/2.22    ( ! [X6,X4,X7,X5,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_1(X3) | m1_subset_1(k5_relat_1(X3,sK3),k1_zfmisc_1(k2_zfmisc_1(X4,k2_relat_1(sK3))))) )),
% 13.68/2.22    inference(resolution,[],[f526,f521])).
% 13.68/2.22  fof(f521,plain,(
% 13.68/2.22    ( ! [X0,X1] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(sK3)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 13.68/2.22    inference(resolution,[],[f508,f136])).
% 13.68/2.22  fof(f508,plain,(
% 13.68/2.22    ( ! [X17,X15,X16] : (~r1_tarski(k2_relat_1(sK3),X15) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X15))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))) )),
% 13.68/2.22    inference(forward_demodulation,[],[f504,f488])).
% 13.68/2.22  fof(f504,plain,(
% 13.68/2.22    ( ! [X17,X15,X16] : (~r1_tarski(k2_relat_1(sK3),X15) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X15))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))) )),
% 13.68/2.22    inference(resolution,[],[f229,f70])).
% 13.68/2.22  fof(f229,plain,(
% 13.68/2.22    ( ! [X6,X4,X5,X3] : (~v1_funct_1(X3) | ~r1_tarski(k2_relat_1(X3),X4) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X3),X4))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) )),
% 13.68/2.22    inference(resolution,[],[f93,f103])).
% 13.68/2.22  fof(f93,plain,(
% 13.68/2.22    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 13.68/2.22    inference(cnf_transformation,[],[f32])).
% 13.68/2.22  fof(f526,plain,(
% 13.68/2.22    ( ! [X30,X33,X31,X34,X32] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) | m1_subset_1(k5_relat_1(X32,sK3),k1_zfmisc_1(k2_zfmisc_1(X33,X31))) | ~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) | ~v1_funct_1(X32)) )),
% 13.68/2.22    inference(resolution,[],[f358,f70])).
% 13.68/2.22  fof(f358,plain,(
% 13.68/2.22    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 13.68/2.22    inference(duplicate_literal_removal,[],[f355])).
% 13.68/2.22  fof(f355,plain,(
% 13.68/2.22    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 13.68/2.22    inference(superposition,[],[f127,f125])).
% 13.68/2.22  fof(f4373,plain,(
% 13.68/2.22    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 13.68/2.22    inference(trivial_inequality_removal,[],[f4371])).
% 13.68/2.22  fof(f4371,plain,(
% 13.68/2.22    ( ! [X2,X0,X3,X1] : (k2_relat_1(sK3) != k2_relat_1(sK3) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 13.68/2.22    inference(resolution,[],[f4352,f136])).
% 13.68/2.22  fof(f4352,plain,(
% 13.68/2.22    ( ! [X4,X2,X0,X3,X1] : (~r1_tarski(k2_relat_1(sK3),X2) | k2_relat_1(sK3) != X2 | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | v1_funct_1(k6_partfun1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 13.68/2.22    inference(subsumption_resolution,[],[f4351,f508])).
% 13.68/2.22  fof(f4351,plain,(
% 13.68/2.22    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relat_1(sK3) != X2 | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | v1_funct_1(k6_partfun1(sK2)) | ~r1_tarski(k2_relat_1(sK3),X2)) )),
% 13.68/2.22    inference(forward_demodulation,[],[f4350,f488])).
% 13.68/2.22  fof(f4350,plain,(
% 13.68/2.22    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relat_1(sK3) != X2 | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X2))) | v1_funct_1(k6_partfun1(sK2)) | ~r1_tarski(k2_relat_1(sK3),X2)) )),
% 13.68/2.22    inference(subsumption_resolution,[],[f4349,f103])).
% 13.68/2.22  fof(f4349,plain,(
% 13.68/2.22    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relat_1(sK3) != X2 | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X2))) | v1_funct_1(k6_partfun1(sK2)) | ~r1_tarski(k2_relat_1(sK3),X2) | ~v1_relat_1(sK3)) )),
% 13.68/2.22    inference(subsumption_resolution,[],[f4346,f70])).
% 13.68/2.22  fof(f4346,plain,(
% 13.68/2.22    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relat_1(sK3) != X2 | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X2))) | v1_funct_1(k6_partfun1(sK2)) | ~r1_tarski(k2_relat_1(sK3),X2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 13.68/2.22    inference(resolution,[],[f2806,f92])).
% 13.68/2.22  fof(f2806,plain,(
% 13.68/2.22    ( ! [X26,X24,X23,X27,X25,X22] : (~v1_funct_2(sK3,X27,X24) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) | k2_relat_1(sK3) != X24 | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X25,X26))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24))) | v1_funct_1(k6_partfun1(sK2))) )),
% 13.68/2.22    inference(forward_demodulation,[],[f2805,f488])).
% 13.68/2.22  fof(f2805,plain,(
% 13.68/2.22    ( ! [X26,X24,X23,X27,X25,X22] : (v1_funct_1(k6_partfun1(k1_relat_1(sK3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) | k2_relat_1(sK3) != X24 | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X25,X26))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24))) | ~v1_funct_2(sK3,X27,X24)) )),
% 13.68/2.22    inference(subsumption_resolution,[],[f2801,f70])).
% 13.68/2.22  fof(f2801,plain,(
% 13.68/2.22    ( ! [X26,X24,X23,X27,X25,X22] : (v1_funct_1(k6_partfun1(k1_relat_1(sK3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) | ~v1_funct_1(sK3) | k2_relat_1(sK3) != X24 | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X25,X26))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X27,X24))) | ~v1_funct_2(sK3,X27,X24)) )),
% 13.68/2.22    inference(resolution,[],[f1474,f77])).
% 13.68/2.22  fof(f1474,plain,(
% 13.68/2.22    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~v2_funct_1(X2) | v1_funct_1(k6_partfun1(k1_relat_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X2) | k2_relat_1(X2) != X1 | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1)) )),
% 13.68/2.22    inference(duplicate_literal_removal,[],[f1473])).
% 13.68/2.22  fof(f1473,plain,(
% 13.68/2.22    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_relat_1(X2) != X1 | v1_funct_1(k6_partfun1(k1_relat_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | ~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 13.68/2.22    inference(superposition,[],[f799,f105])).
% 13.68/2.22  fof(f799,plain,(
% 13.68/2.22    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_relset_1(X5,X6,X0) != X6 | v1_funct_1(k6_partfun1(k1_relat_1(X0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(X0,X5,X6)) )),
% 13.68/2.22    inference(duplicate_literal_removal,[],[f798])).
% 13.68/2.22  fof(f798,plain,(
% 13.68/2.22    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_funct_1(k6_partfun1(k1_relat_1(X0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relset_1(X5,X6,X0) != X6 | ~v2_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(X0,X5,X6) | ~v1_funct_1(X0)) )),
% 13.68/2.22    inference(resolution,[],[f518,f108])).
% 13.68/2.22  fof(f108,plain,(
% 13.68/2.22    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 13.68/2.22    inference(cnf_transformation,[],[f40])).
% 13.68/2.22  fof(f518,plain,(
% 13.68/2.22    ( ! [X6,X8,X7,X5,X9] : (~v1_funct_1(k2_funct_1(X5)) | ~m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | v1_funct_1(k6_partfun1(k1_relat_1(X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_1(X5) | ~v2_funct_1(X5)) )),
% 13.68/2.22    inference(subsumption_resolution,[],[f515,f103])).
% 13.68/2.22  fof(f515,plain,(
% 13.68/2.22    ( ! [X6,X8,X7,X5,X9] : (v1_funct_1(k6_partfun1(k1_relat_1(X5))) | ~m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_1(k2_funct_1(X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_1(X5) | ~v2_funct_1(X5) | ~v1_relat_1(X5)) )),
% 13.68/2.22    inference(duplicate_literal_removal,[],[f513])).
% 13.68/2.22  fof(f513,plain,(
% 13.68/2.22    ( ! [X6,X8,X7,X5,X9] : (v1_funct_1(k6_partfun1(k1_relat_1(X5))) | ~m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_1(k2_funct_1(X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_1(X5) | ~v2_funct_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(X5)) )),
% 13.68/2.22    inference(superposition,[],[f346,f135])).
% 13.68/2.22  fof(f135,plain,(
% 13.68/2.22    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 13.68/2.22    inference(definition_unfolding,[],[f89,f81])).
% 13.68/2.22  fof(f81,plain,(
% 13.68/2.22    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 13.68/2.22    inference(cnf_transformation,[],[f18])).
% 13.68/2.22  fof(f18,axiom,(
% 13.68/2.22    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 13.68/2.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 13.68/2.22  fof(f89,plain,(
% 13.68/2.22    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 13.68/2.22    inference(cnf_transformation,[],[f30])).
% 13.68/2.22  fof(f30,plain,(
% 13.68/2.22    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 13.68/2.22    inference(flattening,[],[f29])).
% 13.68/2.22  fof(f29,plain,(
% 13.68/2.22    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 13.68/2.22    inference(ennf_transformation,[],[f9])).
% 13.68/2.22  fof(f9,axiom,(
% 13.68/2.22    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 13.68/2.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 13.68/2.22  fof(f346,plain,(
% 13.68/2.22    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k5_relat_1(X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 13.68/2.22    inference(duplicate_literal_removal,[],[f345])).
% 13.68/2.22  fof(f345,plain,(
% 13.68/2.22    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k5_relat_1(X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 13.68/2.22    inference(superposition,[],[f126,f125])).
% 13.68/2.22  fof(f126,plain,(
% 13.68/2.22    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 13.68/2.22    inference(cnf_transformation,[],[f48])).
% 13.68/2.22  fof(f4483,plain,(
% 13.68/2.22    ~v1_funct_1(k6_partfun1(sK2)) | k1_xboole_0 = sK2 | k6_partfun1(sK2) = sK4),
% 13.68/2.22    inference(subsumption_resolution,[],[f4481,f136])).
% 13.68/2.22  fof(f4481,plain,(
% 13.68/2.22    ~r1_tarski(sK2,sK2) | ~v1_funct_1(k6_partfun1(sK2)) | k1_xboole_0 = sK2 | k6_partfun1(sK2) = sK4),
% 13.68/2.22    inference(resolution,[],[f4396,f4272])).
% 13.68/2.22  fof(f4272,plain,(
% 13.68/2.22    ~v1_funct_2(k6_partfun1(sK2),sK2,sK2) | ~v1_funct_1(k6_partfun1(sK2)) | k1_xboole_0 = sK2 | k6_partfun1(sK2) = sK4),
% 13.68/2.22    inference(subsumption_resolution,[],[f4271,f72])).
% 13.68/2.22  fof(f4271,plain,(
% 13.68/2.22    ~v1_funct_2(k6_partfun1(sK2),sK2,sK2) | ~v1_funct_1(k6_partfun1(sK2)) | k1_xboole_0 = sK2 | k6_partfun1(sK2) = sK4 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 13.68/2.22    inference(subsumption_resolution,[],[f4268,f85])).
% 13.68/2.22  fof(f85,plain,(
% 13.68/2.22    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 13.68/2.22    inference(cnf_transformation,[],[f16])).
% 13.68/2.22  fof(f16,axiom,(
% 13.68/2.22    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 13.68/2.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 13.68/2.22  fof(f4268,plain,(
% 13.68/2.22    ~v1_funct_2(k6_partfun1(sK2),sK2,sK2) | ~v1_funct_1(k6_partfun1(sK2)) | k1_xboole_0 = sK2 | ~m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | k6_partfun1(sK2) = sK4 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 13.68/2.22    inference(resolution,[],[f4267,f317])).
% 13.68/2.22  fof(f317,plain,(
% 13.68/2.22    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 13.68/2.22    inference(subsumption_resolution,[],[f316,f85])).
% 13.68/2.22  fof(f316,plain,(
% 13.68/2.22    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 13.68/2.22    inference(duplicate_literal_removal,[],[f313])).
% 13.68/2.22  fof(f313,plain,(
% 13.68/2.22    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k5_relat_1(k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 13.68/2.22    inference(superposition,[],[f106,f128])).
% 13.68/2.22  fof(f128,plain,(
% 13.68/2.22    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 13.68/2.22    inference(cnf_transformation,[],[f50])).
% 13.68/2.22  fof(f50,plain,(
% 13.68/2.22    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 13.68/2.22    inference(flattening,[],[f49])).
% 13.68/2.22  fof(f49,plain,(
% 13.68/2.22    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 13.68/2.22    inference(ennf_transformation,[],[f13])).
% 13.68/2.22  fof(f13,axiom,(
% 13.68/2.22    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 13.68/2.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 13.68/2.22  fof(f106,plain,(
% 13.68/2.22    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 13.68/2.22    inference(cnf_transformation,[],[f38])).
% 13.68/2.22  fof(f38,plain,(
% 13.68/2.22    ! [X0,X1,X2] : ((r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 13.68/2.22    inference(ennf_transformation,[],[f19])).
% 13.68/2.22  fof(f19,axiom,(
% 13.68/2.22    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 13.68/2.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).
% 13.68/2.22  fof(f4267,plain,(
% 13.68/2.22    ( ! [X0] : (~r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3) | ~v1_funct_2(X0,sK2,sK2) | ~v1_funct_1(X0) | k1_xboole_0 = sK2 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | sK4 = X0) )),
% 13.68/2.22    inference(subsumption_resolution,[],[f4266,f75])).
% 13.68/2.22  fof(f4266,plain,(
% 13.68/2.22    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X0,sK2,sK2) | ~v1_funct_1(X0) | k1_xboole_0 = sK2 | ~r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3) | sK4 = X0 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))) )),
% 13.68/2.22    inference(duplicate_literal_removal,[],[f4265])).
% 13.68/2.22  fof(f4265,plain,(
% 13.68/2.22    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_2(X0,sK2,sK2) | ~v1_funct_1(X0) | k1_xboole_0 = sK2 | ~r2_relset_1(sK2,sK2,k5_relat_1(X0,sK3),sK3) | sK4 = X0 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))) )),
% 13.68/2.22    inference(resolution,[],[f2701,f123])).
% 13.68/2.22  fof(f4396,plain,(
% 13.68/2.22    ( ! [X0] : (v1_funct_2(k6_partfun1(sK2),sK2,X0) | ~r1_tarski(sK2,X0)) )),
% 13.68/2.22    inference(resolution,[],[f4388,f184])).
% 13.68/2.22  fof(f184,plain,(
% 13.68/2.22    ( ! [X0,X1] : (~v1_funct_1(k6_partfun1(X0)) | v1_funct_2(k6_partfun1(X0),X0,X1) | ~r1_tarski(X0,X1)) )),
% 13.68/2.22    inference(forward_demodulation,[],[f183,f132])).
% 13.68/2.22  fof(f132,plain,(
% 13.68/2.22    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 13.68/2.22    inference(definition_unfolding,[],[f87,f81])).
% 13.68/2.22  fof(f87,plain,(
% 13.68/2.22    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 13.68/2.22    inference(cnf_transformation,[],[f6])).
% 13.68/2.22  fof(f6,axiom,(
% 13.68/2.22    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 13.68/2.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 13.68/2.22  fof(f183,plain,(
% 13.68/2.22    ( ! [X0,X1] : (v1_funct_2(k6_partfun1(X0),X0,X1) | ~r1_tarski(k2_relat_1(k6_partfun1(X0)),X1) | ~v1_funct_1(k6_partfun1(X0))) )),
% 13.68/2.22    inference(subsumption_resolution,[],[f181,f131])).
% 13.68/2.22  fof(f131,plain,(
% 13.68/2.22    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 13.68/2.22    inference(definition_unfolding,[],[f82,f81])).
% 13.68/2.22  fof(f82,plain,(
% 13.68/2.22    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 13.68/2.22    inference(cnf_transformation,[],[f8])).
% 13.68/2.22  fof(f8,axiom,(
% 13.68/2.22    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 13.68/2.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 13.68/2.22  fof(f181,plain,(
% 13.68/2.22    ( ! [X0,X1] : (v1_funct_2(k6_partfun1(X0),X0,X1) | ~r1_tarski(k2_relat_1(k6_partfun1(X0)),X1) | ~v1_funct_1(k6_partfun1(X0)) | ~v1_relat_1(k6_partfun1(X0))) )),
% 13.68/2.22    inference(superposition,[],[f92,f133])).
% 13.68/2.22  fof(f133,plain,(
% 13.68/2.22    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 13.68/2.22    inference(definition_unfolding,[],[f86,f81])).
% 13.68/2.22  fof(f86,plain,(
% 13.68/2.22    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 13.68/2.22    inference(cnf_transformation,[],[f6])).
% 13.68/2.22  fof(f78,plain,(
% 13.68/2.22    ~r2_relset_1(sK2,sK2,sK4,k6_partfun1(sK2))),
% 13.68/2.22    inference(cnf_transformation,[],[f56])).
% 13.68/2.22  fof(f5238,plain,(
% 13.68/2.22    sK3 = k2_zfmisc_1(sK2,sK2)),
% 13.68/2.22    inference(subsumption_resolution,[],[f5237,f80])).
% 13.68/2.22  fof(f80,plain,(
% 13.68/2.22    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 13.68/2.22    inference(cnf_transformation,[],[f2])).
% 13.68/2.23  fof(f2,axiom,(
% 13.68/2.23    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 13.68/2.23    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 13.68/2.23  fof(f5237,plain,(
% 13.68/2.23    ~r1_tarski(k1_xboole_0,sK3) | sK3 = k2_zfmisc_1(sK2,sK2)),
% 13.68/2.23    inference(forward_demodulation,[],[f4694,f138])).
% 13.68/2.23  fof(f4694,plain,(
% 13.68/2.23    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK3) | sK3 = k2_zfmisc_1(sK2,sK2)),
% 13.68/2.23    inference(backward_demodulation,[],[f202,f4688])).
% 13.68/2.23  fof(f202,plain,(
% 13.68/2.23    ~r1_tarski(k2_zfmisc_1(sK2,sK2),sK3) | sK3 = k2_zfmisc_1(sK2,sK2)),
% 13.68/2.23    inference(resolution,[],[f155,f72])).
% 13.68/2.23  fof(f155,plain,(
% 13.68/2.23    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~r1_tarski(X2,X3) | X2 = X3) )),
% 13.68/2.23    inference(resolution,[],[f97,f98])).
% 13.68/2.23  fof(f98,plain,(
% 13.68/2.23    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 13.68/2.23    inference(cnf_transformation,[],[f59])).
% 13.68/2.23  fof(f59,plain,(
% 13.68/2.23    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 13.68/2.23    inference(nnf_transformation,[],[f4])).
% 13.68/2.23  fof(f4,axiom,(
% 13.68/2.23    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 13.68/2.23    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 13.68/2.23  fof(f97,plain,(
% 13.68/2.23    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 13.68/2.23    inference(cnf_transformation,[],[f58])).
% 13.68/2.23  fof(f70,plain,(
% 13.68/2.23    v1_funct_1(sK3)),
% 13.68/2.23    inference(cnf_transformation,[],[f56])).
% 13.68/2.23  fof(f5301,plain,(
% 13.68/2.23    k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0)),
% 13.68/2.23    inference(backward_demodulation,[],[f1313,f5240])).
% 13.68/2.23  fof(f1313,plain,(
% 13.68/2.23    ~v1_funct_1(k1_xboole_0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK3)),
% 13.68/2.23    inference(resolution,[],[f1307,f150])).
% 13.68/2.23  fof(f150,plain,(
% 13.68/2.23    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 13.68/2.23    inference(forward_demodulation,[],[f147,f138])).
% 13.68/2.23  fof(f147,plain,(
% 13.68/2.23    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 13.68/2.23    inference(superposition,[],[f85,f129])).
% 13.68/2.23  fof(f129,plain,(
% 13.68/2.23    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 13.68/2.23    inference(definition_unfolding,[],[f79,f81])).
% 13.68/2.23  fof(f79,plain,(
% 13.68/2.23    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 13.68/2.23    inference(cnf_transformation,[],[f7])).
% 13.68/2.23  fof(f7,axiom,(
% 13.68/2.23    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 13.68/2.23    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 13.68/2.23  fof(f1307,plain,(
% 13.68/2.23    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X0) | k1_xboole_0 = k5_relat_1(X0,sK3)) )),
% 13.68/2.23    inference(forward_demodulation,[],[f1306,f139])).
% 13.68/2.23  fof(f139,plain,(
% 13.68/2.23    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 13.68/2.23    inference(equality_resolution,[],[f101])).
% 13.68/2.23  fof(f101,plain,(
% 13.68/2.23    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 13.68/2.23    inference(cnf_transformation,[],[f61])).
% 13.68/2.23  fof(f1306,plain,(
% 13.68/2.23    ( ! [X0,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k5_relat_1(X0,sK3)) )),
% 13.68/2.23    inference(subsumption_resolution,[],[f1303,f80])).
% 13.68/2.23  fof(f1303,plain,(
% 13.68/2.23    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,k5_relat_1(X0,sK3)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k5_relat_1(X0,sK3)) )),
% 13.68/2.23    inference(superposition,[],[f644,f139])).
% 13.68/2.23  fof(f644,plain,(
% 13.68/2.23    ( ! [X6,X8,X7] : (~r1_tarski(k2_zfmisc_1(X7,sK2),k5_relat_1(X6,sK3)) | ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | k2_zfmisc_1(X7,sK2) = k5_relat_1(X6,sK3)) )),
% 13.68/2.23    inference(resolution,[],[f636,f155])).
% 13.68/2.23  fof(f636,plain,(
% 13.68/2.23    ( ! [X2,X0,X1] : (m1_subset_1(k5_relat_1(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0)) )),
% 13.68/2.23    inference(resolution,[],[f526,f72])).
% 13.68/2.23  fof(f445,plain,(
% 13.68/2.23    ( ! [X0] : (r2_relset_1(k1_xboole_0,X0,k5_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)) )),
% 13.68/2.23    inference(resolution,[],[f413,f150])).
% 13.68/2.23  fof(f413,plain,(
% 13.68/2.23    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | r2_relset_1(k1_xboole_0,X0,k5_relat_1(k1_xboole_0,X1),X1)) )),
% 13.68/2.23    inference(forward_demodulation,[],[f410,f139])).
% 13.68/2.23  fof(f410,plain,(
% 13.68/2.23    ( ! [X0,X1] : (r2_relset_1(k1_xboole_0,X0,k5_relat_1(k1_xboole_0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 13.68/2.23    inference(superposition,[],[f317,f129])).
% 13.68/2.23  fof(f6030,plain,(
% 13.68/2.23    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 13.68/2.23    inference(backward_demodulation,[],[f5236,f5881])).
% 13.68/2.23  fof(f5881,plain,(
% 13.68/2.23    k1_xboole_0 = sK4),
% 13.68/2.23    inference(forward_demodulation,[],[f5880,f138])).
% 13.68/2.23  fof(f5880,plain,(
% 13.68/2.23    sK4 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),
% 13.68/2.23    inference(forward_demodulation,[],[f5879,f4688])).
% 13.68/2.23  fof(f5879,plain,(
% 13.68/2.23    k2_zfmisc_1(sK2,sK2) = sK4),
% 13.68/2.23    inference(subsumption_resolution,[],[f5878,f80])).
% 13.68/2.23  fof(f5878,plain,(
% 13.68/2.23    ~r1_tarski(k1_xboole_0,sK4) | k2_zfmisc_1(sK2,sK2) = sK4),
% 13.68/2.23    inference(forward_demodulation,[],[f4695,f138])).
% 13.68/2.23  fof(f4695,plain,(
% 13.68/2.23    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK4) | k2_zfmisc_1(sK2,sK2) = sK4),
% 13.68/2.23    inference(backward_demodulation,[],[f203,f4688])).
% 13.68/2.23  fof(f203,plain,(
% 13.68/2.23    ~r1_tarski(k2_zfmisc_1(sK2,sK2),sK4) | k2_zfmisc_1(sK2,sK2) = sK4),
% 13.68/2.23    inference(resolution,[],[f155,f75])).
% 13.68/2.23  fof(f5236,plain,(
% 13.68/2.23    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k1_xboole_0)),
% 13.68/2.23    inference(forward_demodulation,[],[f4693,f129])).
% 13.68/2.23  fof(f4693,plain,(
% 13.68/2.23    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK4,k6_partfun1(k1_xboole_0))),
% 13.68/2.23    inference(backward_demodulation,[],[f78,f4688])).
% 13.68/2.23  % SZS output end Proof for theBenchmark
% 13.68/2.23  % (7823)------------------------------
% 13.68/2.23  % (7823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.68/2.23  % (7823)Termination reason: Refutation
% 13.68/2.23  
% 13.68/2.23  % (7823)Memory used [KB]: 14839
% 13.68/2.23  % (7823)Time elapsed: 1.534 s
% 13.68/2.23  % (7823)------------------------------
% 13.68/2.23  % (7823)------------------------------
% 13.68/2.23  % (7800)Success in time 1.873 s
%------------------------------------------------------------------------------
