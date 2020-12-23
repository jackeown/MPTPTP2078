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
% DateTime   : Thu Dec  3 13:05:40 EST 2020

% Result     : Theorem 2.70s
% Output     : Refutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :  238 (44784 expanded)
%              Number of leaves         :   19 (13902 expanded)
%              Depth                    :   45
%              Number of atoms          :  915 (390807 expanded)
%              Number of equality atoms :  236 (7645 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2185,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f1702,f2182,f104])).

fof(f104,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f2182,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1887,f1886])).

fof(f1886,plain,(
    k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f1699,f1815])).

fof(f1815,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f1485,f1164])).

fof(f1164,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f58,f1161])).

fof(f1161,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f1160,f62])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f51,f50])).

fof(f50,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v3_funct_2(X2,sK0,sK0)
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v3_funct_2(X2,sK0,sK0)
        & v1_funct_2(X2,sK0,sK0)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK2,sK0,sK0)
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v3_funct_2(X2,X0,X0)
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
             => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
           => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).

fof(f1160,plain,
    ( k1_xboole_0 = sK0
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f1094,f104])).

fof(f1094,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f135,f1090])).

fof(f1090,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f811,f62])).

fof(f811,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK2 = k2_funct_1(sK1)
      | k1_xboole_0 = sK0 ) ),
    inference(backward_demodulation,[],[f677,f767])).

fof(f767,plain,(
    sK1 = k2_funct_1(sK2) ),
    inference(resolution,[],[f670,f58])).

fof(f670,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK1 = k2_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f669,f55])).

fof(f55,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f669,plain,(
    ! [X0,X1] :
      ( sK1 = k2_funct_1(sK2)
      | ~ v1_funct_1(sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f668,f119])).

fof(f119,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f118,f58])).

fof(f118,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f116,f55])).

fof(f116,plain,
    ( ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k2_relat_1(sK1) ),
    inference(resolution,[],[f115,f57])).

fof(f57,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k2_relat_1(X0) = X2 ) ),
    inference(subsumption_resolution,[],[f114,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k2_relat_1(X0) = X2
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f113,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k2_relat_1(X0) = X2
      | ~ v5_relat_1(X0,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f87,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f668,plain,(
    ! [X0,X1] :
      ( sK0 != k2_relat_1(sK1)
      | sK1 = k2_funct_1(sK2)
      | ~ v1_funct_1(sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(trivial_inequality_removal,[],[f667])).

fof(f667,plain,(
    ! [X0,X1] :
      ( k6_relat_1(sK0) != k6_relat_1(sK0)
      | sK0 != k2_relat_1(sK1)
      | sK1 = k2_funct_1(sK2)
      | ~ v1_funct_1(sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f556,f373])).

fof(f373,plain,(
    k6_relat_1(sK0) = k5_relat_1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f372,f55])).

fof(f372,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK1,sK2)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f371,f58])).

fof(f371,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK1,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f370,f59])).

fof(f59,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f370,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK1,sK2)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f365,f62])).

fof(f365,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(superposition,[],[f243,f93])).

fof(f93,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
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
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f243,plain,(
    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f242,f55])).

fof(f242,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f241,f58])).

fof(f241,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f240,f59])).

fof(f240,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f238,f62])).

fof(f238,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f125,f95])).

fof(f95,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f125,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f122,f97])).

fof(f97,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f67,f65])).

fof(f65,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f122,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0)
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f91,f96])).

fof(f96,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f63,f65])).

fof(f63,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f556,plain,(
    ! [X4,X5,X3] :
      ( k6_relat_1(sK0) != k5_relat_1(X3,sK2)
      | sK0 != k2_relat_1(X3)
      | k2_funct_1(sK2) = X3
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(forward_demodulation,[],[f555,f258])).

fof(f258,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f257,f199])).

fof(f199,plain,(
    sK0 = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f198,f181])).

fof(f181,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f180,f59])).

fof(f180,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f179,f60])).

fof(f60,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f179,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f178,f61])).

fof(f61,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f178,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f174,f62])).

fof(f174,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f81,f138])).

fof(f138,plain,(
    k2_funct_2(sK0,sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f137,f59])).

fof(f137,plain,
    ( k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f136,f61])).

fof(f136,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f131,f62])).

fof(f131,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK2,sK0,sK0)
    | k2_funct_2(sK0,sK2) = k2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f77,f60])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f198,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f197,f193])).

fof(f193,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f192,f59])).

fof(f192,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f191,f60])).

fof(f191,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f190,f61])).

fof(f190,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f177,f62])).

fof(f177,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f78,f138])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f197,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k2_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f185,f115])).

fof(f185,plain,(
    v3_funct_2(k2_funct_1(sK2),sK0,sK0) ),
    inference(subsumption_resolution,[],[f184,f59])).

fof(f184,plain,
    ( v3_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f183,f60])).

fof(f183,plain,
    ( v3_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f182,f61])).

fof(f182,plain,
    ( v3_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f175,f62])).

fof(f175,plain,
    ( v3_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f80,f138])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f257,plain,(
    k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f256,f62])).

fof(f256,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f249,f59])).

fof(f249,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(resolution,[],[f111,f61])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(subsumption_resolution,[],[f110,f82])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f86,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f555,plain,(
    ! [X4,X5,X3] :
      ( k6_relat_1(sK0) != k5_relat_1(X3,sK2)
      | k2_funct_1(sK2) = X3
      | ~ v1_funct_1(X3)
      | k2_relat_1(X3) != k1_relat_1(sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(forward_demodulation,[],[f554,f121])).

fof(f121,plain,(
    sK0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f120,f62])).

fof(f120,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f117,f59])).

fof(f117,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k2_relat_1(sK2) ),
    inference(resolution,[],[f115,f61])).

fof(f554,plain,(
    ! [X4,X5,X3] :
      ( k2_funct_1(sK2) = X3
      | ~ v1_funct_1(X3)
      | k5_relat_1(X3,sK2) != k6_relat_1(k2_relat_1(sK2))
      | k2_relat_1(X3) != k1_relat_1(sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(subsumption_resolution,[],[f553,f62])).

fof(f553,plain,(
    ! [X4,X5,X3] :
      ( k2_funct_1(sK2) = X3
      | ~ v1_funct_1(X3)
      | k5_relat_1(X3,sK2) != k6_relat_1(k2_relat_1(sK2))
      | k2_relat_1(X3) != k1_relat_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(subsumption_resolution,[],[f543,f59])).

fof(f543,plain,(
    ! [X4,X5,X3] :
      ( k2_funct_1(sK2) = X3
      | ~ v1_funct_1(X3)
      | k5_relat_1(X3,sK2) != k6_relat_1(k2_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | k2_relat_1(X3) != k1_relat_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(resolution,[],[f322,f61])).

fof(f322,plain,(
    ! [X6,X10,X8,X7,X5,X9] :
      ( ~ v3_funct_2(X6,X7,X8)
      | k2_funct_1(X6) = X5
      | ~ v1_funct_1(X5)
      | k5_relat_1(X5,X6) != k6_relat_1(k2_relat_1(X6))
      | ~ v1_funct_1(X6)
      | k2_relat_1(X5) != k1_relat_1(X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) ) ),
    inference(resolution,[],[f196,f82])).

fof(f196,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | k2_funct_1(X1) = X0
      | ~ v1_funct_1(X0)
      | k5_relat_1(X0,X1) != k6_relat_1(k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v3_funct_2(X1,X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(subsumption_resolution,[],[f195,f82])).

fof(f195,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relat_1(X0,X1) != k6_relat_1(k2_relat_1(X1))
      | k2_relat_1(X0) != k1_relat_1(X1)
      | k2_funct_1(X1) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v3_funct_2(X1,X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relat_1(X0,X1) != k6_relat_1(k2_relat_1(X1))
      | k2_relat_1(X0) != k1_relat_1(X1)
      | k2_funct_1(X1) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v3_funct_2(X1,X2,X3)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f73,f86])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | k2_funct_1(X0) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f677,plain,(
    ! [X0,X1] :
      ( sK2 = k2_funct_1(k2_funct_1(sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f676,f59])).

fof(f676,plain,(
    ! [X0,X1] :
      ( sK2 = k2_funct_1(k2_funct_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f675,f121])).

fof(f675,plain,(
    ! [X0,X1] :
      ( sK0 != k2_relat_1(sK2)
      | sK2 = k2_funct_1(k2_funct_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = sK0 ) ),
    inference(trivial_inequality_removal,[],[f671])).

fof(f671,plain,(
    ! [X0,X1] :
      ( k6_relat_1(sK0) != k6_relat_1(sK0)
      | sK0 != k2_relat_1(sK2)
      | sK2 = k2_funct_1(k2_funct_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f564,f638])).

fof(f638,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f637,f61])).

fof(f637,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v3_funct_2(sK2,sK0,sK0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f381,f62])).

fof(f381,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
      | ~ v3_funct_2(sK2,X0,X1)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f380,f59])).

fof(f380,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = sK0
      | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
      | ~ v3_funct_2(sK2,X0,X1)
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f234,f86])).

fof(f234,plain,
    ( ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK0
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f233,f59])).

fof(f233,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f232,f60])).

fof(f232,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f231,f62])).

fof(f231,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f228])).

fof(f228,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f100,f227])).

fof(f227,plain,(
    sK0 = k2_relset_1(sK0,sK0,sK2) ),
    inference(subsumption_resolution,[],[f226,f59])).

fof(f226,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f225,f60])).

fof(f225,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f224,f62])).

fof(f224,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f223,f55])).

fof(f223,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK2)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f222,f56])).

fof(f56,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f222,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK2)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f219,f58])).

fof(f219,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f101,f96])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f90,f65])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f88,f65])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f564,plain,(
    ! [X10,X11,X9] :
      ( k6_relat_1(sK0) != k5_relat_1(X9,k2_funct_1(sK2))
      | sK0 != k2_relat_1(X9)
      | k2_funct_1(k2_funct_1(sK2)) = X9
      | ~ v1_funct_1(X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) ) ),
    inference(forward_demodulation,[],[f563,f320])).

fof(f320,plain,(
    sK0 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f262,f319])).

fof(f319,plain,(
    sK0 = k2_relat_1(k2_funct_1(k2_funct_1(sK2))) ),
    inference(subsumption_resolution,[],[f318,f277])).

fof(f277,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f276,f193])).

fof(f276,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f275,f189])).

fof(f189,plain,(
    v1_funct_2(k2_funct_1(sK2),sK0,sK0) ),
    inference(subsumption_resolution,[],[f188,f59])).

fof(f188,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f187,f60])).

fof(f187,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f186,f61])).

fof(f186,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f176,f62])).

fof(f176,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f79,f138])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f275,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f274,f185])).

fof(f274,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f270,f181])).

fof(f270,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f81,f210])).

fof(f210,plain,(
    k2_funct_1(k2_funct_1(sK2)) = k2_funct_2(sK0,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f209,f193])).

fof(f209,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k2_funct_2(sK0,k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f208,f185])).

fof(f208,plain,
    ( ~ v3_funct_2(k2_funct_1(sK2),sK0,sK0)
    | k2_funct_1(k2_funct_1(sK2)) = k2_funct_2(sK0,k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f207,f181])).

fof(f207,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(k2_funct_1(sK2),sK0,sK0)
    | k2_funct_1(k2_funct_1(sK2)) = k2_funct_2(sK0,k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f189,f77])).

fof(f318,plain,
    ( ~ m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k2_relat_1(k2_funct_1(k2_funct_1(sK2))) ),
    inference(subsumption_resolution,[],[f315,f289])).

fof(f289,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1(sK2))) ),
    inference(subsumption_resolution,[],[f288,f193])).

fof(f288,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f287,f189])).

fof(f287,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f286,f185])).

fof(f286,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ v3_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f273,f181])).

fof(f273,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f78,f210])).

fof(f315,plain,
    ( ~ v1_funct_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k2_relat_1(k2_funct_1(k2_funct_1(sK2))) ),
    inference(resolution,[],[f281,f115])).

fof(f281,plain,(
    v3_funct_2(k2_funct_1(k2_funct_1(sK2)),sK0,sK0) ),
    inference(subsumption_resolution,[],[f280,f193])).

fof(f280,plain,
    ( v3_funct_2(k2_funct_1(k2_funct_1(sK2)),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f279,f189])).

fof(f279,plain,
    ( v3_funct_2(k2_funct_1(k2_funct_1(sK2)),sK0,sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f278,f185])).

fof(f278,plain,
    ( v3_funct_2(k2_funct_1(k2_funct_1(sK2)),sK0,sK0)
    | ~ v3_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f271,f181])).

fof(f271,plain,
    ( v3_funct_2(k2_funct_1(k2_funct_1(sK2)),sK0,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f80,f210])).

fof(f262,plain,(
    k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(k2_funct_1(sK2))) ),
    inference(subsumption_resolution,[],[f261,f181])).

fof(f261,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(k2_funct_1(sK2))) ),
    inference(subsumption_resolution,[],[f251,f193])).

fof(f251,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(k2_funct_1(sK2))) ),
    inference(resolution,[],[f111,f185])).

fof(f563,plain,(
    ! [X10,X11,X9] :
      ( k6_relat_1(sK0) != k5_relat_1(X9,k2_funct_1(sK2))
      | k2_funct_1(k2_funct_1(sK2)) = X9
      | ~ v1_funct_1(X9)
      | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) ) ),
    inference(forward_demodulation,[],[f562,f199])).

fof(f562,plain,(
    ! [X10,X11,X9] :
      ( k2_funct_1(k2_funct_1(sK2)) = X9
      | ~ v1_funct_1(X9)
      | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k5_relat_1(X9,k2_funct_1(sK2))
      | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) ) ),
    inference(subsumption_resolution,[],[f561,f181])).

fof(f561,plain,(
    ! [X10,X11,X9] :
      ( k2_funct_1(k2_funct_1(sK2)) = X9
      | ~ v1_funct_1(X9)
      | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k5_relat_1(X9,k2_funct_1(sK2))
      | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(X9)
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) ) ),
    inference(subsumption_resolution,[],[f545,f193])).

fof(f545,plain,(
    ! [X10,X11,X9] :
      ( k2_funct_1(k2_funct_1(sK2)) = X9
      | ~ v1_funct_1(X9)
      | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k5_relat_1(X9,k2_funct_1(sK2))
      | ~ v1_funct_1(k2_funct_1(sK2))
      | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(X9)
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) ) ),
    inference(resolution,[],[f322,f185])).

fof(f135,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f64,f134])).

fof(f134,plain,(
    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f133,f55])).

fof(f133,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f132,f57])).

fof(f132,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f130,f58])).

fof(f130,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f77,f56])).

fof(f64,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f58,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f1485,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f1258,f82])).

fof(f1258,plain,
    ( ~ v1_relat_1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f1171])).

fof(f1171,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | ~ v1_relat_1(sK1) ),
    inference(backward_demodulation,[],[f127,f1161])).

fof(f127,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f69,f119])).

fof(f69,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f1699,plain,(
    sK1 = k2_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f767,f1697])).

fof(f1697,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f1482,f1167])).

fof(f1167,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f62,f1161])).

fof(f1482,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = sK2 ) ),
    inference(resolution,[],[f1257,f82])).

fof(f1257,plain,
    ( ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f1173])).

fof(f1173,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f129,f1161])).

fof(f129,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f69,f121])).

fof(f1887,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f1704,f1815])).

fof(f1704,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f1175,f1697])).

fof(f1175,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f135,f1161])).

fof(f1702,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f1167,f1697])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:15:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.56  % (10706)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.56  % (10698)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.57  % (10707)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.57  % (10714)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.57  % (10722)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.58  % (10714)Refutation not found, incomplete strategy% (10714)------------------------------
% 0.22/0.58  % (10714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (10720)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.59  % (10702)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.59  % (10703)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.60  % (10699)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.60  % (10704)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.60  % (10701)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.86/0.60  % (10714)Termination reason: Refutation not found, incomplete strategy
% 1.86/0.60  
% 1.86/0.60  % (10714)Memory used [KB]: 10746
% 1.86/0.60  % (10714)Time elapsed: 0.148 s
% 1.86/0.60  % (10714)------------------------------
% 1.86/0.60  % (10714)------------------------------
% 1.86/0.61  % (10721)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.86/0.61  % (10700)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.86/0.62  % (10724)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.86/0.62  % (10705)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.86/0.62  % (10713)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 2.08/0.63  % (10715)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 2.08/0.63  % (10726)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 2.08/0.63  % (10719)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 2.08/0.63  % (10716)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 2.08/0.63  % (10717)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 2.08/0.64  % (10723)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 2.08/0.64  % (10712)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 2.08/0.64  % (10718)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 2.08/0.64  % (10709)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 2.08/0.64  % (10710)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 2.16/0.64  % (10727)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 2.16/0.64  % (10711)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 2.16/0.65  % (10725)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 2.16/0.65  % (10708)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 2.70/0.77  % (10720)Refutation found. Thanks to Tanya!
% 2.70/0.77  % SZS status Theorem for theBenchmark
% 3.17/0.79  % SZS output start Proof for theBenchmark
% 3.17/0.79  fof(f2185,plain,(
% 3.17/0.79    $false),
% 3.17/0.79    inference(unit_resulting_resolution,[],[f1702,f2182,f104])).
% 3.17/0.79  fof(f104,plain,(
% 3.17/0.79    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.17/0.79    inference(duplicate_literal_removal,[],[f103])).
% 3.17/0.79  fof(f103,plain,(
% 3.17/0.79    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.17/0.79    inference(equality_resolution,[],[f92])).
% 3.17/0.79  fof(f92,plain,(
% 3.17/0.79    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.17/0.79    inference(cnf_transformation,[],[f54])).
% 3.17/0.79  fof(f54,plain,(
% 3.17/0.79    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.17/0.79    inference(nnf_transformation,[],[f45])).
% 3.17/0.79  fof(f45,plain,(
% 3.17/0.79    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.17/0.79    inference(flattening,[],[f44])).
% 3.17/0.79  fof(f44,plain,(
% 3.17/0.79    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.17/0.79    inference(ennf_transformation,[],[f8])).
% 3.17/0.79  fof(f8,axiom,(
% 3.17/0.79    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.17/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 3.17/0.79  fof(f2182,plain,(
% 3.17/0.79    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 3.17/0.79    inference(forward_demodulation,[],[f1887,f1886])).
% 3.17/0.79  fof(f1886,plain,(
% 3.17/0.79    k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 3.17/0.79    inference(backward_demodulation,[],[f1699,f1815])).
% 3.17/0.79  fof(f1815,plain,(
% 3.17/0.79    k1_xboole_0 = sK1),
% 3.17/0.79    inference(resolution,[],[f1485,f1164])).
% 3.17/0.79  fof(f1164,plain,(
% 3.17/0.79    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 3.17/0.79    inference(backward_demodulation,[],[f58,f1161])).
% 3.17/0.79  fof(f1161,plain,(
% 3.17/0.79    k1_xboole_0 = sK0),
% 3.17/0.79    inference(subsumption_resolution,[],[f1160,f62])).
% 3.17/0.79  fof(f62,plain,(
% 3.17/0.79    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.17/0.79    inference(cnf_transformation,[],[f52])).
% 3.17/0.79  fof(f52,plain,(
% 3.17/0.79    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.17/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f51,f50])).
% 3.17/0.79  fof(f50,plain,(
% 3.17/0.79    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.17/0.79    introduced(choice_axiom,[])).
% 3.17/0.79  fof(f51,plain,(
% 3.17/0.79    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 3.17/0.79    introduced(choice_axiom,[])).
% 3.17/0.79  fof(f22,plain,(
% 3.17/0.79    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.17/0.79    inference(flattening,[],[f21])).
% 3.17/0.79  fof(f21,plain,(
% 3.17/0.79    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.17/0.79    inference(ennf_transformation,[],[f20])).
% 3.17/0.79  fof(f20,negated_conjecture,(
% 3.17/0.79    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.17/0.79    inference(negated_conjecture,[],[f19])).
% 3.17/0.79  fof(f19,conjecture,(
% 3.17/0.79    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.17/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).
% 3.17/0.79  fof(f1160,plain,(
% 3.17/0.79    k1_xboole_0 = sK0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.17/0.79    inference(resolution,[],[f1094,f104])).
% 3.17/0.79  fof(f1094,plain,(
% 3.17/0.79    ~r2_relset_1(sK0,sK0,sK2,sK2) | k1_xboole_0 = sK0),
% 3.17/0.79    inference(superposition,[],[f135,f1090])).
% 3.17/0.79  fof(f1090,plain,(
% 3.17/0.79    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0),
% 3.17/0.79    inference(resolution,[],[f811,f62])).
% 3.17/0.79  fof(f811,plain,(
% 3.17/0.79    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0) )),
% 3.17/0.79    inference(backward_demodulation,[],[f677,f767])).
% 3.17/0.79  fof(f767,plain,(
% 3.17/0.79    sK1 = k2_funct_1(sK2)),
% 3.17/0.79    inference(resolution,[],[f670,f58])).
% 3.17/0.79  fof(f670,plain,(
% 3.17/0.79    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK1 = k2_funct_1(sK2)) )),
% 3.17/0.79    inference(subsumption_resolution,[],[f669,f55])).
% 3.17/0.79  fof(f55,plain,(
% 3.17/0.79    v1_funct_1(sK1)),
% 3.17/0.79    inference(cnf_transformation,[],[f52])).
% 3.17/0.79  fof(f669,plain,(
% 3.17/0.79    ( ! [X0,X1] : (sK1 = k2_funct_1(sK2) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.17/0.79    inference(subsumption_resolution,[],[f668,f119])).
% 3.17/0.79  fof(f119,plain,(
% 3.17/0.79    sK0 = k2_relat_1(sK1)),
% 3.17/0.79    inference(subsumption_resolution,[],[f118,f58])).
% 3.17/0.79  fof(f118,plain,(
% 3.17/0.79    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 = k2_relat_1(sK1)),
% 3.17/0.79    inference(subsumption_resolution,[],[f116,f55])).
% 3.17/0.79  fof(f116,plain,(
% 3.17/0.79    ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 = k2_relat_1(sK1)),
% 3.17/0.79    inference(resolution,[],[f115,f57])).
% 3.17/0.79  fof(f57,plain,(
% 3.17/0.79    v3_funct_2(sK1,sK0,sK0)),
% 3.17/0.79    inference(cnf_transformation,[],[f52])).
% 3.17/0.79  fof(f115,plain,(
% 3.17/0.79    ( ! [X2,X0,X1] : (~v3_funct_2(X0,X1,X2) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k2_relat_1(X0) = X2) )),
% 3.17/0.79    inference(subsumption_resolution,[],[f114,f82])).
% 3.17/0.79  fof(f82,plain,(
% 3.17/0.79    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.17/0.79    inference(cnf_transformation,[],[f36])).
% 3.17/0.79  fof(f36,plain,(
% 3.17/0.79    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.17/0.79    inference(ennf_transformation,[],[f6])).
% 3.17/0.79  fof(f6,axiom,(
% 3.17/0.79    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.17/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 3.17/0.79  fof(f114,plain,(
% 3.17/0.79    ( ! [X2,X0,X1] : (~v3_funct_2(X0,X1,X2) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k2_relat_1(X0) = X2 | ~v1_relat_1(X0)) )),
% 3.17/0.79    inference(subsumption_resolution,[],[f113,f84])).
% 3.17/0.79  fof(f84,plain,(
% 3.17/0.79    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.17/0.79    inference(cnf_transformation,[],[f37])).
% 3.17/0.79  fof(f37,plain,(
% 3.17/0.79    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.17/0.79    inference(ennf_transformation,[],[f7])).
% 3.17/0.79  fof(f7,axiom,(
% 3.17/0.79    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.17/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 3.17/0.79  fof(f113,plain,(
% 3.17/0.79    ( ! [X2,X0,X1] : (~v3_funct_2(X0,X1,X2) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k2_relat_1(X0) = X2 | ~v5_relat_1(X0,X2) | ~v1_relat_1(X0)) )),
% 3.17/0.79    inference(resolution,[],[f87,f75])).
% 3.17/0.79  fof(f75,plain,(
% 3.17/0.79    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.17/0.79    inference(cnf_transformation,[],[f53])).
% 3.17/0.79  fof(f53,plain,(
% 3.17/0.79    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.17/0.79    inference(nnf_transformation,[],[f31])).
% 3.17/0.79  fof(f31,plain,(
% 3.17/0.79    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.17/0.79    inference(flattening,[],[f30])).
% 3.17/0.79  fof(f30,plain,(
% 3.17/0.79    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.17/0.79    inference(ennf_transformation,[],[f10])).
% 3.17/0.79  fof(f10,axiom,(
% 3.17/0.79    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.17/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 3.17/0.79  fof(f87,plain,(
% 3.17/0.79    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.17/0.79    inference(cnf_transformation,[],[f39])).
% 3.17/0.79  fof(f39,plain,(
% 3.17/0.79    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.17/0.79    inference(flattening,[],[f38])).
% 3.17/0.79  fof(f38,plain,(
% 3.17/0.79    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.17/0.79    inference(ennf_transformation,[],[f9])).
% 3.17/0.79  fof(f9,axiom,(
% 3.17/0.79    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.17/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 3.17/0.79  fof(f668,plain,(
% 3.17/0.79    ( ! [X0,X1] : (sK0 != k2_relat_1(sK1) | sK1 = k2_funct_1(sK2) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.17/0.79    inference(trivial_inequality_removal,[],[f667])).
% 3.17/0.79  fof(f667,plain,(
% 3.17/0.79    ( ! [X0,X1] : (k6_relat_1(sK0) != k6_relat_1(sK0) | sK0 != k2_relat_1(sK1) | sK1 = k2_funct_1(sK2) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.17/0.79    inference(superposition,[],[f556,f373])).
% 3.17/0.79  fof(f373,plain,(
% 3.17/0.79    k6_relat_1(sK0) = k5_relat_1(sK1,sK2)),
% 3.17/0.79    inference(subsumption_resolution,[],[f372,f55])).
% 3.17/0.79  fof(f372,plain,(
% 3.17/0.79    k6_relat_1(sK0) = k5_relat_1(sK1,sK2) | ~v1_funct_1(sK1)),
% 3.17/0.79    inference(subsumption_resolution,[],[f371,f58])).
% 3.17/0.79  fof(f371,plain,(
% 3.17/0.79    k6_relat_1(sK0) = k5_relat_1(sK1,sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 3.17/0.79    inference(subsumption_resolution,[],[f370,f59])).
% 3.17/0.79  fof(f59,plain,(
% 3.17/0.79    v1_funct_1(sK2)),
% 3.17/0.79    inference(cnf_transformation,[],[f52])).
% 3.17/0.79  fof(f370,plain,(
% 3.17/0.79    k6_relat_1(sK0) = k5_relat_1(sK1,sK2) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 3.17/0.79    inference(subsumption_resolution,[],[f365,f62])).
% 3.17/0.79  fof(f365,plain,(
% 3.17/0.79    k6_relat_1(sK0) = k5_relat_1(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 3.17/0.79    inference(superposition,[],[f243,f93])).
% 3.17/0.79  fof(f93,plain,(
% 3.17/0.79    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.17/0.79    inference(cnf_transformation,[],[f47])).
% 3.17/0.79  fof(f47,plain,(
% 3.17/0.79    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.17/0.79    inference(flattening,[],[f46])).
% 3.17/0.79  fof(f46,plain,(
% 3.17/0.79    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.17/0.79    inference(ennf_transformation,[],[f14])).
% 3.17/0.79  fof(f14,axiom,(
% 3.17/0.79    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 3.17/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 3.17/0.79  fof(f243,plain,(
% 3.17/0.79    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0)),
% 3.17/0.79    inference(subsumption_resolution,[],[f242,f55])).
% 3.17/0.79  fof(f242,plain,(
% 3.17/0.79    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0) | ~v1_funct_1(sK1)),
% 3.17/0.79    inference(subsumption_resolution,[],[f241,f58])).
% 3.17/0.79  fof(f241,plain,(
% 3.17/0.79    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 3.17/0.79    inference(subsumption_resolution,[],[f240,f59])).
% 3.17/0.79  fof(f240,plain,(
% 3.17/0.79    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 3.17/0.79    inference(subsumption_resolution,[],[f238,f62])).
% 3.17/0.79  fof(f238,plain,(
% 3.17/0.79    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 3.17/0.79    inference(resolution,[],[f125,f95])).
% 3.17/0.79  fof(f95,plain,(
% 3.17/0.79    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.17/0.79    inference(cnf_transformation,[],[f49])).
% 3.17/0.79  fof(f49,plain,(
% 3.17/0.79    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.17/0.79    inference(flattening,[],[f48])).
% 3.17/0.79  fof(f48,plain,(
% 3.17/0.79    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.17/0.79    inference(ennf_transformation,[],[f11])).
% 3.17/0.79  fof(f11,axiom,(
% 3.17/0.79    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.17/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 3.17/0.79  fof(f125,plain,(
% 3.17/0.79    ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0)),
% 3.17/0.79    inference(subsumption_resolution,[],[f122,f97])).
% 3.17/0.79  fof(f97,plain,(
% 3.17/0.79    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.17/0.79    inference(definition_unfolding,[],[f67,f65])).
% 3.17/0.79  fof(f65,plain,(
% 3.17/0.79    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 3.17/0.79    inference(cnf_transformation,[],[f16])).
% 3.17/0.79  fof(f16,axiom,(
% 3.17/0.79    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 3.17/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 3.17/0.79  fof(f67,plain,(
% 3.17/0.79    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.17/0.79    inference(cnf_transformation,[],[f13])).
% 3.17/0.79  fof(f13,axiom,(
% 3.17/0.79    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.17/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 3.17/0.79  fof(f122,plain,(
% 3.17/0.79    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.17/0.79    inference(resolution,[],[f91,f96])).
% 3.17/0.79  fof(f96,plain,(
% 3.17/0.79    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0))),
% 3.17/0.79    inference(definition_unfolding,[],[f63,f65])).
% 3.17/0.79  fof(f63,plain,(
% 3.17/0.79    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 3.17/0.79    inference(cnf_transformation,[],[f52])).
% 3.17/0.79  fof(f91,plain,(
% 3.17/0.79    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.17/0.79    inference(cnf_transformation,[],[f54])).
% 3.17/0.79  fof(f556,plain,(
% 3.17/0.79    ( ! [X4,X5,X3] : (k6_relat_1(sK0) != k5_relat_1(X3,sK2) | sK0 != k2_relat_1(X3) | k2_funct_1(sK2) = X3 | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 3.17/0.79    inference(forward_demodulation,[],[f555,f258])).
% 3.17/0.79  fof(f258,plain,(
% 3.17/0.79    sK0 = k1_relat_1(sK2)),
% 3.17/0.79    inference(forward_demodulation,[],[f257,f199])).
% 3.17/0.79  fof(f199,plain,(
% 3.17/0.79    sK0 = k2_relat_1(k2_funct_1(sK2))),
% 3.17/0.79    inference(subsumption_resolution,[],[f198,f181])).
% 3.17/0.79  fof(f181,plain,(
% 3.17/0.79    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.17/0.79    inference(subsumption_resolution,[],[f180,f59])).
% 3.17/0.79  fof(f180,plain,(
% 3.17/0.79    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 3.17/0.79    inference(subsumption_resolution,[],[f179,f60])).
% 3.17/0.79  fof(f60,plain,(
% 3.17/0.79    v1_funct_2(sK2,sK0,sK0)),
% 3.17/0.79    inference(cnf_transformation,[],[f52])).
% 3.17/0.79  fof(f179,plain,(
% 3.17/0.79    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 3.17/0.79    inference(subsumption_resolution,[],[f178,f61])).
% 3.17/0.79  fof(f61,plain,(
% 3.17/0.79    v3_funct_2(sK2,sK0,sK0)),
% 3.17/0.79    inference(cnf_transformation,[],[f52])).
% 3.17/0.79  fof(f178,plain,(
% 3.17/0.79    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 3.17/0.79    inference(subsumption_resolution,[],[f174,f62])).
% 3.17/0.79  fof(f174,plain,(
% 3.17/0.79    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 3.17/0.79    inference(superposition,[],[f81,f138])).
% 3.17/0.79  fof(f138,plain,(
% 3.17/0.79    k2_funct_2(sK0,sK2) = k2_funct_1(sK2)),
% 3.17/0.79    inference(subsumption_resolution,[],[f137,f59])).
% 3.17/0.79  fof(f137,plain,(
% 3.17/0.79    k2_funct_2(sK0,sK2) = k2_funct_1(sK2) | ~v1_funct_1(sK2)),
% 3.17/0.79    inference(subsumption_resolution,[],[f136,f61])).
% 3.17/0.79  fof(f136,plain,(
% 3.17/0.79    ~v3_funct_2(sK2,sK0,sK0) | k2_funct_2(sK0,sK2) = k2_funct_1(sK2) | ~v1_funct_1(sK2)),
% 3.17/0.79    inference(subsumption_resolution,[],[f131,f62])).
% 3.17/0.79  fof(f131,plain,(
% 3.17/0.79    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK2,sK0,sK0) | k2_funct_2(sK0,sK2) = k2_funct_1(sK2) | ~v1_funct_1(sK2)),
% 3.17/0.79    inference(resolution,[],[f77,f60])).
% 3.17/0.79  fof(f77,plain,(
% 3.17/0.79    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v1_funct_1(X1)) )),
% 3.17/0.79    inference(cnf_transformation,[],[f33])).
% 3.17/0.79  fof(f33,plain,(
% 3.17/0.79    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.17/0.79    inference(flattening,[],[f32])).
% 3.17/0.79  fof(f32,plain,(
% 3.17/0.79    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.17/0.79    inference(ennf_transformation,[],[f15])).
% 3.17/0.79  fof(f15,axiom,(
% 3.17/0.79    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 3.17/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 3.17/0.79  fof(f81,plain,(
% 3.17/0.79    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.17/0.79    inference(cnf_transformation,[],[f35])).
% 3.17/0.79  fof(f35,plain,(
% 3.17/0.79    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.17/0.79    inference(flattening,[],[f34])).
% 3.17/0.79  fof(f34,plain,(
% 3.17/0.79    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.17/0.79    inference(ennf_transformation,[],[f12])).
% 3.17/0.79  fof(f12,axiom,(
% 3.17/0.79    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.17/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 3.17/0.79  fof(f198,plain,(
% 3.17/0.79    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 = k2_relat_1(k2_funct_1(sK2))),
% 3.17/0.79    inference(subsumption_resolution,[],[f197,f193])).
% 3.17/0.79  fof(f193,plain,(
% 3.17/0.79    v1_funct_1(k2_funct_1(sK2))),
% 3.17/0.79    inference(subsumption_resolution,[],[f192,f59])).
% 3.17/0.79  fof(f192,plain,(
% 3.17/0.79    v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 3.17/0.79    inference(subsumption_resolution,[],[f191,f60])).
% 3.17/0.79  fof(f191,plain,(
% 3.17/0.79    v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 3.17/0.79    inference(subsumption_resolution,[],[f190,f61])).
% 3.17/0.79  fof(f190,plain,(
% 3.17/0.79    v1_funct_1(k2_funct_1(sK2)) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 3.17/0.79    inference(subsumption_resolution,[],[f177,f62])).
% 3.17/0.79  fof(f177,plain,(
% 3.17/0.79    v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 3.17/0.79    inference(superposition,[],[f78,f138])).
% 3.17/0.79  fof(f78,plain,(
% 3.17/0.79    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.17/0.79    inference(cnf_transformation,[],[f35])).
% 3.17/0.79  fof(f197,plain,(
% 3.17/0.79    ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 = k2_relat_1(k2_funct_1(sK2))),
% 3.17/0.79    inference(resolution,[],[f185,f115])).
% 3.17/0.79  fof(f185,plain,(
% 3.17/0.79    v3_funct_2(k2_funct_1(sK2),sK0,sK0)),
% 3.17/0.79    inference(subsumption_resolution,[],[f184,f59])).
% 3.17/0.79  fof(f184,plain,(
% 3.17/0.79    v3_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v1_funct_1(sK2)),
% 3.17/0.79    inference(subsumption_resolution,[],[f183,f60])).
% 3.17/0.79  fof(f183,plain,(
% 3.17/0.79    v3_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 3.17/0.79    inference(subsumption_resolution,[],[f182,f61])).
% 3.17/0.79  fof(f182,plain,(
% 3.17/0.79    v3_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 3.17/0.79    inference(subsumption_resolution,[],[f175,f62])).
% 3.17/0.79  fof(f175,plain,(
% 3.17/0.79    v3_funct_2(k2_funct_1(sK2),sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 3.17/0.79    inference(superposition,[],[f80,f138])).
% 3.17/0.79  fof(f80,plain,(
% 3.17/0.79    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.17/0.79    inference(cnf_transformation,[],[f35])).
% 3.17/0.79  fof(f257,plain,(
% 3.17/0.79    k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)),
% 3.17/0.79    inference(subsumption_resolution,[],[f256,f62])).
% 3.17/0.79  fof(f256,plain,(
% 3.17/0.79    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)),
% 3.17/0.79    inference(subsumption_resolution,[],[f249,f59])).
% 3.17/0.79  fof(f249,plain,(
% 3.17/0.79    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)),
% 3.17/0.79    inference(resolution,[],[f111,f61])).
% 3.17/0.79  fof(f111,plain,(
% 3.17/0.79    ( ! [X2,X0,X1] : (~v3_funct_2(X0,X1,X2) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 3.17/0.79    inference(subsumption_resolution,[],[f110,f82])).
% 3.17/0.79  fof(f110,plain,(
% 3.17/0.79    ( ! [X2,X0,X1] : (~v3_funct_2(X0,X1,X2) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 3.17/0.79    inference(duplicate_literal_removal,[],[f107])).
% 3.17/0.79  fof(f107,plain,(
% 3.17/0.79    ( ! [X2,X0,X1] : (~v3_funct_2(X0,X1,X2) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.17/0.79    inference(resolution,[],[f86,f72])).
% 3.17/0.79  fof(f72,plain,(
% 3.17/0.79    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.17/0.79    inference(cnf_transformation,[],[f27])).
% 3.17/0.79  fof(f27,plain,(
% 3.17/0.79    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.17/0.79    inference(flattening,[],[f26])).
% 3.17/0.79  fof(f26,plain,(
% 3.17/0.79    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.17/0.79    inference(ennf_transformation,[],[f4])).
% 3.17/0.79  fof(f4,axiom,(
% 3.17/0.79    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.17/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 3.17/0.79  fof(f86,plain,(
% 3.17/0.79    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.17/0.79    inference(cnf_transformation,[],[f39])).
% 3.17/0.79  fof(f555,plain,(
% 3.17/0.79    ( ! [X4,X5,X3] : (k6_relat_1(sK0) != k5_relat_1(X3,sK2) | k2_funct_1(sK2) = X3 | ~v1_funct_1(X3) | k2_relat_1(X3) != k1_relat_1(sK2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 3.17/0.79    inference(forward_demodulation,[],[f554,f121])).
% 3.17/0.79  fof(f121,plain,(
% 3.17/0.79    sK0 = k2_relat_1(sK2)),
% 3.17/0.79    inference(subsumption_resolution,[],[f120,f62])).
% 3.17/0.79  fof(f120,plain,(
% 3.17/0.79    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 = k2_relat_1(sK2)),
% 3.17/0.79    inference(subsumption_resolution,[],[f117,f59])).
% 3.17/0.79  fof(f117,plain,(
% 3.17/0.79    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 = k2_relat_1(sK2)),
% 3.17/0.79    inference(resolution,[],[f115,f61])).
% 3.17/0.79  fof(f554,plain,(
% 3.17/0.79    ( ! [X4,X5,X3] : (k2_funct_1(sK2) = X3 | ~v1_funct_1(X3) | k5_relat_1(X3,sK2) != k6_relat_1(k2_relat_1(sK2)) | k2_relat_1(X3) != k1_relat_1(sK2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 3.17/0.79    inference(subsumption_resolution,[],[f553,f62])).
% 3.17/0.79  fof(f553,plain,(
% 3.17/0.79    ( ! [X4,X5,X3] : (k2_funct_1(sK2) = X3 | ~v1_funct_1(X3) | k5_relat_1(X3,sK2) != k6_relat_1(k2_relat_1(sK2)) | k2_relat_1(X3) != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 3.17/0.79    inference(subsumption_resolution,[],[f543,f59])).
% 3.17/0.79  fof(f543,plain,(
% 3.17/0.79    ( ! [X4,X5,X3] : (k2_funct_1(sK2) = X3 | ~v1_funct_1(X3) | k5_relat_1(X3,sK2) != k6_relat_1(k2_relat_1(sK2)) | ~v1_funct_1(sK2) | k2_relat_1(X3) != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 3.17/0.79    inference(resolution,[],[f322,f61])).
% 3.17/0.79  fof(f322,plain,(
% 3.17/0.79    ( ! [X6,X10,X8,X7,X5,X9] : (~v3_funct_2(X6,X7,X8) | k2_funct_1(X6) = X5 | ~v1_funct_1(X5) | k5_relat_1(X5,X6) != k6_relat_1(k2_relat_1(X6)) | ~v1_funct_1(X6) | k2_relat_1(X5) != k1_relat_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))) )),
% 3.17/0.79    inference(resolution,[],[f196,f82])).
% 3.17/0.79  fof(f196,plain,(
% 3.17/0.79    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | k2_relat_1(X0) != k1_relat_1(X1) | k2_funct_1(X1) = X0 | ~v1_funct_1(X0) | k5_relat_1(X0,X1) != k6_relat_1(k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v3_funct_2(X1,X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 3.17/0.79    inference(subsumption_resolution,[],[f195,f82])).
% 3.17/0.79  fof(f195,plain,(
% 3.17/0.79    ( ! [X2,X0,X3,X1] : (k5_relat_1(X0,X1) != k6_relat_1(k2_relat_1(X1)) | k2_relat_1(X0) != k1_relat_1(X1) | k2_funct_1(X1) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v3_funct_2(X1,X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 3.17/0.79    inference(duplicate_literal_removal,[],[f194])).
% 3.17/0.79  fof(f194,plain,(
% 3.17/0.79    ( ! [X2,X0,X3,X1] : (k5_relat_1(X0,X1) != k6_relat_1(k2_relat_1(X1)) | k2_relat_1(X0) != k1_relat_1(X1) | k2_funct_1(X1) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v3_funct_2(X1,X2,X3) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 3.17/0.79    inference(resolution,[],[f73,f86])).
% 3.17/0.79  fof(f73,plain,(
% 3.17/0.79    ( ! [X0,X1] : (~v2_funct_1(X0) | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | k2_funct_1(X0) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.17/0.79    inference(cnf_transformation,[],[f29])).
% 3.17/0.79  fof(f29,plain,(
% 3.17/0.79    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.17/0.79    inference(flattening,[],[f28])).
% 3.17/0.79  fof(f28,plain,(
% 3.17/0.79    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.17/0.79    inference(ennf_transformation,[],[f5])).
% 3.17/0.79  fof(f5,axiom,(
% 3.17/0.79    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.17/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 3.17/0.79  fof(f677,plain,(
% 3.17/0.79    ( ! [X0,X1] : (sK2 = k2_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = sK0) )),
% 3.17/0.79    inference(subsumption_resolution,[],[f676,f59])).
% 3.17/0.79  fof(f676,plain,(
% 3.17/0.79    ( ! [X0,X1] : (sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = sK0) )),
% 3.17/0.79    inference(subsumption_resolution,[],[f675,f121])).
% 3.17/0.79  fof(f675,plain,(
% 3.17/0.79    ( ! [X0,X1] : (sK0 != k2_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = sK0) )),
% 3.17/0.79    inference(trivial_inequality_removal,[],[f671])).
% 3.17/0.79  fof(f671,plain,(
% 3.17/0.79    ( ! [X0,X1] : (k6_relat_1(sK0) != k6_relat_1(sK0) | sK0 != k2_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = sK0) )),
% 3.17/0.79    inference(superposition,[],[f564,f638])).
% 3.17/0.79  fof(f638,plain,(
% 3.17/0.79    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | k1_xboole_0 = sK0),
% 3.17/0.79    inference(subsumption_resolution,[],[f637,f61])).
% 3.17/0.79  fof(f637,plain,(
% 3.17/0.79    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v3_funct_2(sK2,sK0,sK0) | k1_xboole_0 = sK0),
% 3.17/0.79    inference(resolution,[],[f381,f62])).
% 3.17/0.79  fof(f381,plain,(
% 3.17/0.79    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v3_funct_2(sK2,X0,X1) | k1_xboole_0 = sK0) )),
% 3.17/0.79    inference(subsumption_resolution,[],[f380,f59])).
% 3.17/0.79  fof(f380,plain,(
% 3.17/0.79    ( ! [X0,X1] : (k1_xboole_0 = sK0 | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v3_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.17/0.79    inference(resolution,[],[f234,f86])).
% 3.17/0.79  fof(f234,plain,(
% 3.17/0.79    ~v2_funct_1(sK2) | k1_xboole_0 = sK0 | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 3.17/0.79    inference(subsumption_resolution,[],[f233,f59])).
% 3.17/0.79  fof(f233,plain,(
% 3.17/0.79    k1_xboole_0 = sK0 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 3.17/0.79    inference(subsumption_resolution,[],[f232,f60])).
% 3.17/0.79  fof(f232,plain,(
% 3.17/0.79    k1_xboole_0 = sK0 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 3.17/0.79    inference(subsumption_resolution,[],[f231,f62])).
% 3.17/0.79  fof(f231,plain,(
% 3.17/0.79    k1_xboole_0 = sK0 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 3.17/0.79    inference(trivial_inequality_removal,[],[f228])).
% 3.17/0.79  fof(f228,plain,(
% 3.17/0.79    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 3.17/0.79    inference(superposition,[],[f100,f227])).
% 3.17/0.79  fof(f227,plain,(
% 3.17/0.79    sK0 = k2_relset_1(sK0,sK0,sK2)),
% 3.17/0.79    inference(subsumption_resolution,[],[f226,f59])).
% 3.17/0.79  fof(f226,plain,(
% 3.17/0.79    sK0 = k2_relset_1(sK0,sK0,sK2) | ~v1_funct_1(sK2)),
% 3.17/0.79    inference(subsumption_resolution,[],[f225,f60])).
% 3.17/0.79  fof(f225,plain,(
% 3.17/0.79    sK0 = k2_relset_1(sK0,sK0,sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 3.17/0.79    inference(subsumption_resolution,[],[f224,f62])).
% 3.17/0.79  fof(f224,plain,(
% 3.17/0.79    sK0 = k2_relset_1(sK0,sK0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 3.17/0.79    inference(subsumption_resolution,[],[f223,f55])).
% 3.17/0.79  fof(f223,plain,(
% 3.17/0.79    sK0 = k2_relset_1(sK0,sK0,sK2) | ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 3.17/0.79    inference(subsumption_resolution,[],[f222,f56])).
% 3.17/0.79  fof(f56,plain,(
% 3.17/0.79    v1_funct_2(sK1,sK0,sK0)),
% 3.17/0.79    inference(cnf_transformation,[],[f52])).
% 3.17/0.79  fof(f222,plain,(
% 3.17/0.79    sK0 = k2_relset_1(sK0,sK0,sK2) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 3.17/0.79    inference(subsumption_resolution,[],[f219,f58])).
% 3.17/0.79  fof(f219,plain,(
% 3.17/0.79    sK0 = k2_relset_1(sK0,sK0,sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 3.17/0.79    inference(resolution,[],[f101,f96])).
% 3.17/0.79  fof(f101,plain,(
% 3.17/0.79    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.17/0.79    inference(definition_unfolding,[],[f90,f65])).
% 3.17/0.79  fof(f90,plain,(
% 3.17/0.79    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.17/0.79    inference(cnf_transformation,[],[f43])).
% 3.17/0.79  fof(f43,plain,(
% 3.17/0.79    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.17/0.79    inference(flattening,[],[f42])).
% 3.17/0.79  fof(f42,plain,(
% 3.17/0.79    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.17/0.79    inference(ennf_transformation,[],[f17])).
% 3.17/0.79  fof(f17,axiom,(
% 3.17/0.79    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.17/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 3.17/0.79  fof(f100,plain,(
% 3.17/0.79    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.17/0.79    inference(definition_unfolding,[],[f88,f65])).
% 3.17/0.79  fof(f88,plain,(
% 3.17/0.79    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.17/0.79    inference(cnf_transformation,[],[f41])).
% 3.17/0.79  fof(f41,plain,(
% 3.17/0.79    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.17/0.79    inference(flattening,[],[f40])).
% 3.17/0.79  fof(f40,plain,(
% 3.17/0.79    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.17/0.79    inference(ennf_transformation,[],[f18])).
% 3.17/0.79  fof(f18,axiom,(
% 3.17/0.79    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 3.17/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 3.17/0.79  fof(f564,plain,(
% 3.17/0.79    ( ! [X10,X11,X9] : (k6_relat_1(sK0) != k5_relat_1(X9,k2_funct_1(sK2)) | sK0 != k2_relat_1(X9) | k2_funct_1(k2_funct_1(sK2)) = X9 | ~v1_funct_1(X9) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) )),
% 3.17/0.79    inference(forward_demodulation,[],[f563,f320])).
% 3.17/0.79  fof(f320,plain,(
% 3.17/0.79    sK0 = k1_relat_1(k2_funct_1(sK2))),
% 3.17/0.79    inference(backward_demodulation,[],[f262,f319])).
% 3.17/0.79  fof(f319,plain,(
% 3.17/0.79    sK0 = k2_relat_1(k2_funct_1(k2_funct_1(sK2)))),
% 3.17/0.79    inference(subsumption_resolution,[],[f318,f277])).
% 3.17/0.79  fof(f277,plain,(
% 3.17/0.79    m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.17/0.79    inference(subsumption_resolution,[],[f276,f193])).
% 3.17/0.79  fof(f276,plain,(
% 3.17/0.79    m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.17/0.79    inference(subsumption_resolution,[],[f275,f189])).
% 3.17/0.79  fof(f189,plain,(
% 3.17/0.79    v1_funct_2(k2_funct_1(sK2),sK0,sK0)),
% 3.17/0.79    inference(subsumption_resolution,[],[f188,f59])).
% 3.17/0.79  fof(f188,plain,(
% 3.17/0.79    v1_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v1_funct_1(sK2)),
% 3.17/0.79    inference(subsumption_resolution,[],[f187,f60])).
% 3.17/0.79  fof(f187,plain,(
% 3.17/0.79    v1_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 3.17/0.79    inference(subsumption_resolution,[],[f186,f61])).
% 3.17/0.79  fof(f186,plain,(
% 3.17/0.79    v1_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 3.17/0.79    inference(subsumption_resolution,[],[f176,f62])).
% 3.17/0.79  fof(f176,plain,(
% 3.17/0.79    v1_funct_2(k2_funct_1(sK2),sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 3.17/0.79    inference(superposition,[],[f79,f138])).
% 3.17/0.79  fof(f79,plain,(
% 3.17/0.79    ( ! [X0,X1] : (v1_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.17/0.79    inference(cnf_transformation,[],[f35])).
% 3.17/0.79  fof(f275,plain,(
% 3.17/0.79    m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.17/0.79    inference(subsumption_resolution,[],[f274,f185])).
% 3.17/0.79  fof(f274,plain,(
% 3.17/0.79    m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v1_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.17/0.79    inference(subsumption_resolution,[],[f270,f181])).
% 3.17/0.79  fof(f270,plain,(
% 3.17/0.79    m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v1_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.17/0.79    inference(superposition,[],[f81,f210])).
% 3.17/0.79  fof(f210,plain,(
% 3.17/0.79    k2_funct_1(k2_funct_1(sK2)) = k2_funct_2(sK0,k2_funct_1(sK2))),
% 3.17/0.79    inference(subsumption_resolution,[],[f209,f193])).
% 3.17/0.79  fof(f209,plain,(
% 3.17/0.79    k2_funct_1(k2_funct_1(sK2)) = k2_funct_2(sK0,k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.17/0.79    inference(subsumption_resolution,[],[f208,f185])).
% 3.17/0.79  fof(f208,plain,(
% 3.17/0.79    ~v3_funct_2(k2_funct_1(sK2),sK0,sK0) | k2_funct_1(k2_funct_1(sK2)) = k2_funct_2(sK0,k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.17/0.79    inference(subsumption_resolution,[],[f207,f181])).
% 3.17/0.79  fof(f207,plain,(
% 3.17/0.79    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(k2_funct_1(sK2),sK0,sK0) | k2_funct_1(k2_funct_1(sK2)) = k2_funct_2(sK0,k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.17/0.79    inference(resolution,[],[f189,f77])).
% 3.17/0.79  fof(f318,plain,(
% 3.17/0.79    ~m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 = k2_relat_1(k2_funct_1(k2_funct_1(sK2)))),
% 3.17/0.79    inference(subsumption_resolution,[],[f315,f289])).
% 3.17/0.79  fof(f289,plain,(
% 3.17/0.79    v1_funct_1(k2_funct_1(k2_funct_1(sK2)))),
% 3.17/0.79    inference(subsumption_resolution,[],[f288,f193])).
% 3.17/0.79  fof(f288,plain,(
% 3.17/0.79    v1_funct_1(k2_funct_1(k2_funct_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.17/0.79    inference(subsumption_resolution,[],[f287,f189])).
% 3.17/0.79  fof(f287,plain,(
% 3.17/0.79    v1_funct_1(k2_funct_1(k2_funct_1(sK2))) | ~v1_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.17/0.79    inference(subsumption_resolution,[],[f286,f185])).
% 3.17/0.79  fof(f286,plain,(
% 3.17/0.79    v1_funct_1(k2_funct_1(k2_funct_1(sK2))) | ~v3_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v1_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.17/0.79    inference(subsumption_resolution,[],[f273,f181])).
% 3.17/0.79  fof(f273,plain,(
% 3.17/0.79    v1_funct_1(k2_funct_1(k2_funct_1(sK2))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v1_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.17/0.79    inference(superposition,[],[f78,f210])).
% 3.17/0.79  fof(f315,plain,(
% 3.17/0.79    ~v1_funct_1(k2_funct_1(k2_funct_1(sK2))) | ~m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 = k2_relat_1(k2_funct_1(k2_funct_1(sK2)))),
% 3.17/0.79    inference(resolution,[],[f281,f115])).
% 3.17/0.79  fof(f281,plain,(
% 3.17/0.79    v3_funct_2(k2_funct_1(k2_funct_1(sK2)),sK0,sK0)),
% 3.17/0.79    inference(subsumption_resolution,[],[f280,f193])).
% 3.17/0.79  fof(f280,plain,(
% 3.17/0.79    v3_funct_2(k2_funct_1(k2_funct_1(sK2)),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.17/0.79    inference(subsumption_resolution,[],[f279,f189])).
% 3.17/0.79  fof(f279,plain,(
% 3.17/0.79    v3_funct_2(k2_funct_1(k2_funct_1(sK2)),sK0,sK0) | ~v1_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.17/0.79    inference(subsumption_resolution,[],[f278,f185])).
% 3.17/0.79  fof(f278,plain,(
% 3.17/0.79    v3_funct_2(k2_funct_1(k2_funct_1(sK2)),sK0,sK0) | ~v3_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v1_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.17/0.79    inference(subsumption_resolution,[],[f271,f181])).
% 3.17/0.79  fof(f271,plain,(
% 3.17/0.79    v3_funct_2(k2_funct_1(k2_funct_1(sK2)),sK0,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v1_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.17/0.79    inference(superposition,[],[f80,f210])).
% 3.17/0.79  fof(f262,plain,(
% 3.17/0.79    k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(k2_funct_1(sK2)))),
% 3.17/0.79    inference(subsumption_resolution,[],[f261,f181])).
% 3.17/0.79  fof(f261,plain,(
% 3.17/0.79    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(k2_funct_1(sK2)))),
% 3.17/0.79    inference(subsumption_resolution,[],[f251,f193])).
% 3.17/0.79  fof(f251,plain,(
% 3.17/0.79    ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(k2_funct_1(sK2)))),
% 3.17/0.79    inference(resolution,[],[f111,f185])).
% 3.17/0.79  fof(f563,plain,(
% 3.17/0.79    ( ! [X10,X11,X9] : (k6_relat_1(sK0) != k5_relat_1(X9,k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = X9 | ~v1_funct_1(X9) | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(X9) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) )),
% 3.17/0.79    inference(forward_demodulation,[],[f562,f199])).
% 3.17/0.79  fof(f562,plain,(
% 3.17/0.79    ( ! [X10,X11,X9] : (k2_funct_1(k2_funct_1(sK2)) = X9 | ~v1_funct_1(X9) | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k5_relat_1(X9,k2_funct_1(sK2)) | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(X9) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) )),
% 3.17/0.79    inference(subsumption_resolution,[],[f561,f181])).
% 3.17/0.79  fof(f561,plain,(
% 3.17/0.79    ( ! [X10,X11,X9] : (k2_funct_1(k2_funct_1(sK2)) = X9 | ~v1_funct_1(X9) | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k5_relat_1(X9,k2_funct_1(sK2)) | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(X9) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) )),
% 3.17/0.79    inference(subsumption_resolution,[],[f545,f193])).
% 3.17/0.79  fof(f545,plain,(
% 3.17/0.79    ( ! [X10,X11,X9] : (k2_funct_1(k2_funct_1(sK2)) = X9 | ~v1_funct_1(X9) | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k5_relat_1(X9,k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(X9) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) )),
% 3.17/0.79    inference(resolution,[],[f322,f185])).
% 3.17/0.79  fof(f135,plain,(
% 3.17/0.79    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))),
% 3.17/0.79    inference(backward_demodulation,[],[f64,f134])).
% 3.17/0.79  fof(f134,plain,(
% 3.17/0.79    k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 3.17/0.79    inference(subsumption_resolution,[],[f133,f55])).
% 3.17/0.79  fof(f133,plain,(
% 3.17/0.79    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 3.17/0.79    inference(subsumption_resolution,[],[f132,f57])).
% 3.17/0.79  fof(f132,plain,(
% 3.17/0.79    ~v3_funct_2(sK1,sK0,sK0) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 3.17/0.79    inference(subsumption_resolution,[],[f130,f58])).
% 3.17/0.79  fof(f130,plain,(
% 3.17/0.79    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 3.17/0.79    inference(resolution,[],[f77,f56])).
% 3.17/0.79  fof(f64,plain,(
% 3.17/0.79    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 3.17/0.79    inference(cnf_transformation,[],[f52])).
% 3.17/0.79  fof(f58,plain,(
% 3.17/0.79    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.17/0.79    inference(cnf_transformation,[],[f52])).
% 3.17/0.79  fof(f1485,plain,(
% 3.17/0.79    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = sK1) )),
% 3.17/0.79    inference(resolution,[],[f1258,f82])).
% 3.17/0.79  fof(f1258,plain,(
% 3.17/0.79    ~v1_relat_1(sK1) | k1_xboole_0 = sK1),
% 3.17/0.79    inference(trivial_inequality_removal,[],[f1171])).
% 3.17/0.79  fof(f1171,plain,(
% 3.17/0.79    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | ~v1_relat_1(sK1)),
% 3.17/0.79    inference(backward_demodulation,[],[f127,f1161])).
% 3.17/0.79  fof(f127,plain,(
% 3.17/0.79    k1_xboole_0 != sK0 | k1_xboole_0 = sK1 | ~v1_relat_1(sK1)),
% 3.17/0.79    inference(superposition,[],[f69,f119])).
% 3.17/0.79  fof(f69,plain,(
% 3.17/0.79    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 3.17/0.79    inference(cnf_transformation,[],[f24])).
% 3.17/0.79  fof(f24,plain,(
% 3.17/0.79    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 3.17/0.79    inference(flattening,[],[f23])).
% 3.17/0.79  fof(f23,plain,(
% 3.17/0.79    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 3.17/0.79    inference(ennf_transformation,[],[f3])).
% 3.17/0.79  fof(f3,axiom,(
% 3.17/0.79    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 3.17/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 3.17/0.79  fof(f1699,plain,(
% 3.17/0.79    sK1 = k2_funct_1(k1_xboole_0)),
% 3.17/0.79    inference(backward_demodulation,[],[f767,f1697])).
% 3.17/0.79  fof(f1697,plain,(
% 3.17/0.79    k1_xboole_0 = sK2),
% 3.17/0.79    inference(resolution,[],[f1482,f1167])).
% 3.17/0.79  fof(f1167,plain,(
% 3.17/0.79    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 3.17/0.79    inference(backward_demodulation,[],[f62,f1161])).
% 3.17/0.79  fof(f1482,plain,(
% 3.17/0.79    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = sK2) )),
% 3.17/0.79    inference(resolution,[],[f1257,f82])).
% 3.17/0.79  fof(f1257,plain,(
% 3.17/0.79    ~v1_relat_1(sK2) | k1_xboole_0 = sK2),
% 3.17/0.79    inference(trivial_inequality_removal,[],[f1173])).
% 3.17/0.79  fof(f1173,plain,(
% 3.17/0.79    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | ~v1_relat_1(sK2)),
% 3.17/0.79    inference(backward_demodulation,[],[f129,f1161])).
% 3.17/0.79  fof(f129,plain,(
% 3.17/0.79    k1_xboole_0 != sK0 | k1_xboole_0 = sK2 | ~v1_relat_1(sK2)),
% 3.17/0.79    inference(superposition,[],[f69,f121])).
% 3.17/0.79  fof(f1887,plain,(
% 3.17/0.79    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0))),
% 3.17/0.79    inference(backward_demodulation,[],[f1704,f1815])).
% 3.17/0.79  fof(f1704,plain,(
% 3.17/0.79    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1))),
% 3.17/0.79    inference(backward_demodulation,[],[f1175,f1697])).
% 3.17/0.79  fof(f1175,plain,(
% 3.17/0.79    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1))),
% 3.17/0.79    inference(backward_demodulation,[],[f135,f1161])).
% 3.17/0.79  fof(f1702,plain,(
% 3.17/0.79    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 3.17/0.79    inference(backward_demodulation,[],[f1167,f1697])).
% 3.17/0.79  % SZS output end Proof for theBenchmark
% 3.17/0.79  % (10720)------------------------------
% 3.17/0.79  % (10720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.17/0.79  % (10720)Termination reason: Refutation
% 3.17/0.79  
% 3.17/0.79  % (10720)Memory used [KB]: 7419
% 3.17/0.79  % (10720)Time elapsed: 0.316 s
% 3.17/0.79  % (10720)------------------------------
% 3.17/0.79  % (10720)------------------------------
% 3.17/0.80  % (10696)Success in time 0.431 s
%------------------------------------------------------------------------------
