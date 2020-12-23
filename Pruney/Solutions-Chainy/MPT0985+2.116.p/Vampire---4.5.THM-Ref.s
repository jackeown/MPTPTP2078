%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :  142 (5636 expanded)
%              Number of leaves         :   14 (1346 expanded)
%              Depth                    :   32
%              Number of atoms          :  389 (32976 expanded)
%              Number of equality atoms :  126 (5588 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1281,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1280,f449])).

fof(f449,plain,(
    ! [X2] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f448,f230])).

fof(f230,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f215,f113])).

fof(f113,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f63,f89])).

fof(f89,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f64,f51])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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

fof(f215,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    inference(resolution,[],[f208,f64])).

fof(f208,plain,(
    ! [X0] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f201,f175])).

fof(f175,plain,(
    ! [X0,X1] : k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0) ),
    inference(resolution,[],[f71,f51])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f201,plain,(
    ! [X0,X1] : m1_subset_1(k1_relset_1(X0,X1,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f72,f51])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f448,plain,(
    ! [X2] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,k1_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f447,f83])).

fof(f83,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f447,plain,(
    ! [X2,X3] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,k1_relat_1(k2_zfmisc_1(k1_xboole_0,X3))) ),
    inference(forward_demodulation,[],[f428,f83])).

fof(f428,plain,(
    ! [X2,X3] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2),X3))) ),
    inference(resolution,[],[f368,f113])).

fof(f368,plain,(
    ! [X2,X0,X1] : r1_tarski(k1_relset_1(X0,X1,k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))),X0) ),
    inference(resolution,[],[f303,f64])).

fof(f303,plain,(
    ! [X4,X2,X3] : m1_subset_1(k1_relset_1(X2,X3,k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))),k1_zfmisc_1(X2)) ),
    inference(resolution,[],[f298,f72])).

fof(f298,plain,(
    ! [X0,X1] : m1_subset_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f289,f194])).

fof(f194,plain,(
    ! [X0,X1] : k1_relat_1(k2_zfmisc_1(X0,X1)) = k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) ),
    inference(resolution,[],[f179,f80])).

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f179,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,k2_zfmisc_1(X2,X3))
      | k1_relset_1(X2,X3,X4) = k1_relat_1(X4) ) ),
    inference(resolution,[],[f71,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f289,plain,(
    ! [X0,X1] : m1_subset_1(k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f205,f80])).

fof(f205,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,k2_zfmisc_1(X2,X3))
      | m1_subset_1(k1_relset_1(X2,X3,X4),k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f72,f65])).

fof(f1280,plain,(
    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1279,f51])).

fof(f1279,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) ),
    inference(resolution,[],[f1278,f572])).

fof(f572,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(forward_demodulation,[],[f87,f83])).

fof(f87,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f34])).

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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f1278,plain,(
    ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f1277,f1075])).

fof(f1075,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f45,f1049])).

fof(f1049,plain,(
    k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f1048,f82])).

fof(f82,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1048,plain,(
    sK2 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1047,f89])).

fof(f1047,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1027,f82])).

fof(f1027,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2)
    | sK2 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(superposition,[],[f114,f1021])).

fof(f1021,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f1020,f93])).

fof(f93,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f69,f47])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f1020,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f1019,f45])).

fof(f1019,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f1018,f57])).

fof(f57,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f1018,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f50,f988,f997])).

fof(f997,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f987,f549])).

fof(f549,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f544,f69])).

fof(f544,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f543,f142])).

fof(f142,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f137,f49])).

fof(f49,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f137,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f70,f47])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f543,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f542,f129])).

fof(f129,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f128,f93])).

fof(f128,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f127,f45])).

fof(f127,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f58,f48])).

fof(f48,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

% (8502)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
fof(f58,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f542,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f541,f133])).

fof(f133,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f132,f93])).

fof(f132,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f131,f45])).

fof(f131,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f59,f48])).

% (8497)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f59,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f541,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) ),
    inference(subsumption_resolution,[],[f539,f93])).

fof(f539,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f122,f45])).

fof(f122,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)))))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f120,f56])).

fof(f56,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f120,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)))))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f55,f57])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f987,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f502,f972])).

fof(f972,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f971,f176])).

fof(f176,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f71,f47])).

fof(f971,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f969,f47])).

fof(f969,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f73,f46])).

fof(f46,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f502,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f135,f142])).

fof(f135,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f134,f129])).

fof(f134,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f54,f133])).

fof(f54,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f988,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f544,f972])).

fof(f50,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f114,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f63,f90])).

fof(f90,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f64,f47])).

fof(f45,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f1277,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f1276,f1175])).

fof(f1175,plain,(
    k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f1060,f1049])).

fof(f1060,plain,(
    k1_xboole_0 = k2_funct_1(sK2) ),
    inference(forward_demodulation,[],[f1059,f83])).

fof(f1059,plain,(
    k2_funct_1(sK2) = k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f1058,f89])).

fof(f1058,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_funct_1(sK2))
    | k2_funct_1(sK2) = k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f1042,f83])).

fof(f1042,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)),k2_funct_1(sK2))
    | k2_funct_1(sK2) = k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)) ),
    inference(superposition,[],[f562,f1021])).

fof(f562,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,k1_relat_1(sK2)),k2_funct_1(sK2))
    | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2)) ),
    inference(resolution,[],[f550,f63])).

fof(f550,plain,(
    r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2))) ),
    inference(resolution,[],[f544,f64])).

fof(f1276,plain,
    ( ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f1275,f1049])).

fof(f1275,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f1274,f1175])).

fof(f1274,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f1273,f1049])).

fof(f1273,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f1272,f51])).

fof(f1272,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f1271,f1175])).

fof(f1271,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f1045,f1049])).

fof(f1045,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f1025,f83])).

fof(f1025,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f50,f1021])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:29:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (8485)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (8486)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (8493)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (8492)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.54  % (8486)Refutation not found, incomplete strategy% (8486)------------------------------
% 0.22/0.54  % (8486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (8486)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (8486)Memory used [KB]: 10618
% 0.22/0.54  % (8486)Time elapsed: 0.119 s
% 0.22/0.54  % (8486)------------------------------
% 0.22/0.54  % (8486)------------------------------
% 0.22/0.54  % (8491)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.54  % (8480)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.54  % (8482)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.55  % (8501)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.55  % (8505)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.55  % (8494)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.55  % (8484)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.56  % (8483)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.57  % (8496)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.57  % (8500)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.58  % (8488)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.58  % (8481)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.58  % (8503)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.59  % (8495)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.59  % (8501)Refutation found. Thanks to Tanya!
% 0.22/0.59  % SZS status Theorem for theBenchmark
% 0.22/0.59  % SZS output start Proof for theBenchmark
% 0.22/0.59  fof(f1281,plain,(
% 0.22/0.59    $false),
% 0.22/0.59    inference(subsumption_resolution,[],[f1280,f449])).
% 0.22/0.59  fof(f449,plain,(
% 0.22/0.59    ( ! [X2] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,k1_xboole_0)) )),
% 0.22/0.59    inference(forward_demodulation,[],[f448,f230])).
% 0.22/0.59  fof(f230,plain,(
% 0.22/0.59    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.59    inference(resolution,[],[f215,f113])).
% 0.22/0.59  fof(f113,plain,(
% 0.22/0.59    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 0.22/0.59    inference(resolution,[],[f63,f89])).
% 0.22/0.59  fof(f89,plain,(
% 0.22/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.59    inference(resolution,[],[f64,f51])).
% 0.22/0.59  fof(f51,plain,(
% 0.22/0.59    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f3])).
% 0.22/0.59  fof(f3,axiom,(
% 0.22/0.59    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.59  fof(f64,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f41])).
% 0.22/0.59  fof(f41,plain,(
% 0.22/0.59    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.59    inference(nnf_transformation,[],[f4])).
% 0.22/0.59  fof(f4,axiom,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.59  fof(f63,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.59    inference(cnf_transformation,[],[f40])).
% 0.22/0.59  fof(f40,plain,(
% 0.22/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.59    inference(flattening,[],[f39])).
% 0.22/0.59  fof(f39,plain,(
% 0.22/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.59    inference(nnf_transformation,[],[f1])).
% 0.22/0.59  fof(f1,axiom,(
% 0.22/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.59  fof(f215,plain,(
% 0.22/0.59    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) )),
% 0.22/0.59    inference(resolution,[],[f208,f64])).
% 0.22/0.59  fof(f208,plain,(
% 0.22/0.59    ( ! [X0] : (m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X0))) )),
% 0.22/0.59    inference(forward_demodulation,[],[f201,f175])).
% 0.22/0.59  fof(f175,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)) )),
% 0.22/0.59    inference(resolution,[],[f71,f51])).
% 0.22/0.59  fof(f71,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f31])).
% 0.22/0.59  fof(f31,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.59    inference(ennf_transformation,[],[f12])).
% 0.22/0.59  fof(f12,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.59  fof(f201,plain,(
% 0.22/0.59    ( ! [X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 0.22/0.59    inference(resolution,[],[f72,f51])).
% 0.22/0.59  fof(f72,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f32])).
% 0.22/0.59  fof(f32,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.59    inference(ennf_transformation,[],[f11])).
% 0.22/0.59  fof(f11,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.22/0.59  fof(f448,plain,(
% 0.22/0.59    ( ! [X2] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,k1_relat_1(k1_xboole_0))) )),
% 0.22/0.59    inference(forward_demodulation,[],[f447,f83])).
% 0.22/0.59  fof(f83,plain,(
% 0.22/0.59    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.59    inference(equality_resolution,[],[f67])).
% 0.22/0.59  fof(f67,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.22/0.59    inference(cnf_transformation,[],[f43])).
% 0.22/0.59  fof(f43,plain,(
% 0.22/0.59    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.22/0.59    inference(flattening,[],[f42])).
% 0.22/0.59  fof(f42,plain,(
% 0.22/0.59    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.22/0.59    inference(nnf_transformation,[],[f2])).
% 0.22/0.59  fof(f2,axiom,(
% 0.22/0.59    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.59  fof(f447,plain,(
% 0.22/0.59    ( ! [X2,X3] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,k1_relat_1(k2_zfmisc_1(k1_xboole_0,X3)))) )),
% 0.22/0.59    inference(forward_demodulation,[],[f428,f83])).
% 0.22/0.59  fof(f428,plain,(
% 0.22/0.59    ( ! [X2,X3] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2),X3)))) )),
% 0.22/0.59    inference(resolution,[],[f368,f113])).
% 0.22/0.59  fof(f368,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (r1_tarski(k1_relset_1(X0,X1,k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))),X0)) )),
% 0.22/0.59    inference(resolution,[],[f303,f64])).
% 0.22/0.59  fof(f303,plain,(
% 0.22/0.59    ( ! [X4,X2,X3] : (m1_subset_1(k1_relset_1(X2,X3,k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))),k1_zfmisc_1(X2))) )),
% 0.22/0.59    inference(resolution,[],[f298,f72])).
% 0.22/0.59  fof(f298,plain,(
% 0.22/0.59    ( ! [X0,X1] : (m1_subset_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k1_zfmisc_1(X0))) )),
% 0.22/0.59    inference(forward_demodulation,[],[f289,f194])).
% 0.22/0.59  fof(f194,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.59    inference(resolution,[],[f179,f80])).
% 0.22/0.59  fof(f80,plain,(
% 0.22/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.59    inference(equality_resolution,[],[f62])).
% 0.22/0.59  fof(f62,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.59    inference(cnf_transformation,[],[f40])).
% 0.22/0.59  fof(f179,plain,(
% 0.22/0.59    ( ! [X4,X2,X3] : (~r1_tarski(X4,k2_zfmisc_1(X2,X3)) | k1_relset_1(X2,X3,X4) = k1_relat_1(X4)) )),
% 0.22/0.59    inference(resolution,[],[f71,f65])).
% 0.22/0.59  fof(f65,plain,(
% 0.22/0.59    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f41])).
% 0.22/0.59  fof(f289,plain,(
% 0.22/0.59    ( ! [X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)),k1_zfmisc_1(X0))) )),
% 0.22/0.59    inference(resolution,[],[f205,f80])).
% 0.22/0.59  fof(f205,plain,(
% 0.22/0.59    ( ! [X4,X2,X3] : (~r1_tarski(X4,k2_zfmisc_1(X2,X3)) | m1_subset_1(k1_relset_1(X2,X3,X4),k1_zfmisc_1(X2))) )),
% 0.22/0.59    inference(resolution,[],[f72,f65])).
% 0.22/0.59  fof(f1280,plain,(
% 0.22/0.59    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0)),
% 0.22/0.59    inference(subsumption_resolution,[],[f1279,f51])).
% 0.22/0.59  fof(f1279,plain,(
% 0.22/0.59    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0)),
% 0.22/0.59    inference(resolution,[],[f1278,f572])).
% 0.22/0.59  fof(f572,plain,(
% 0.22/0.59    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.22/0.59    inference(forward_demodulation,[],[f87,f83])).
% 0.22/0.59  fof(f87,plain,(
% 0.22/0.59    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.22/0.59    inference(equality_resolution,[],[f76])).
% 0.22/0.59  fof(f76,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f44])).
% 0.22/0.59  fof(f44,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.59    inference(nnf_transformation,[],[f34])).
% 0.22/0.59  fof(f34,plain,(
% 0.22/0.59    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.59    inference(flattening,[],[f33])).
% 0.22/0.59  fof(f33,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.59    inference(ennf_transformation,[],[f14])).
% 0.22/0.59  fof(f14,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.59  fof(f1278,plain,(
% 0.22/0.59    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)),
% 0.22/0.59    inference(subsumption_resolution,[],[f1277,f1075])).
% 0.22/0.59  fof(f1075,plain,(
% 0.22/0.59    v1_funct_1(k1_xboole_0)),
% 0.22/0.59    inference(superposition,[],[f45,f1049])).
% 0.22/0.59  fof(f1049,plain,(
% 0.22/0.59    k1_xboole_0 = sK2),
% 0.22/0.59    inference(forward_demodulation,[],[f1048,f82])).
% 0.22/0.59  fof(f82,plain,(
% 0.22/0.59    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.59    inference(equality_resolution,[],[f68])).
% 0.22/0.59  fof(f68,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.22/0.59    inference(cnf_transformation,[],[f43])).
% 0.22/0.59  fof(f1048,plain,(
% 0.22/0.59    sK2 = k2_zfmisc_1(sK0,k1_xboole_0)),
% 0.22/0.59    inference(subsumption_resolution,[],[f1047,f89])).
% 0.22/0.59  fof(f1047,plain,(
% 0.22/0.59    ~r1_tarski(k1_xboole_0,sK2) | sK2 = k2_zfmisc_1(sK0,k1_xboole_0)),
% 0.22/0.59    inference(forward_demodulation,[],[f1027,f82])).
% 0.22/0.59  fof(f1027,plain,(
% 0.22/0.59    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2) | sK2 = k2_zfmisc_1(sK0,k1_xboole_0)),
% 0.22/0.59    inference(superposition,[],[f114,f1021])).
% 0.22/0.59  fof(f1021,plain,(
% 0.22/0.59    k1_xboole_0 = sK1),
% 0.22/0.59    inference(subsumption_resolution,[],[f1020,f93])).
% 0.22/0.59  fof(f93,plain,(
% 0.22/0.59    v1_relat_1(sK2)),
% 0.22/0.59    inference(resolution,[],[f69,f47])).
% 0.22/0.59  fof(f47,plain,(
% 0.22/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.59    inference(cnf_transformation,[],[f38])).
% 0.22/0.59  fof(f38,plain,(
% 0.22/0.59    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.22/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f37])).
% 0.22/0.59  fof(f37,plain,(
% 0.22/0.59    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f19,plain,(
% 0.22/0.59    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.59    inference(flattening,[],[f18])).
% 0.22/0.59  fof(f18,plain,(
% 0.22/0.59    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.59    inference(ennf_transformation,[],[f17])).
% 0.22/0.59  fof(f17,negated_conjecture,(
% 0.22/0.59    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.59    inference(negated_conjecture,[],[f16])).
% 0.22/0.59  fof(f16,conjecture,(
% 0.22/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.59  fof(f69,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f29])).
% 0.22/0.59  fof(f29,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.59    inference(ennf_transformation,[],[f10])).
% 0.22/0.59  fof(f10,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.59  fof(f1020,plain,(
% 0.22/0.59    k1_xboole_0 = sK1 | ~v1_relat_1(sK2)),
% 0.22/0.59    inference(subsumption_resolution,[],[f1019,f45])).
% 0.22/0.59  fof(f1019,plain,(
% 0.22/0.59    k1_xboole_0 = sK1 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.59    inference(resolution,[],[f1018,f57])).
% 0.22/0.59  fof(f57,plain,(
% 0.22/0.59    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f24])).
% 0.22/0.59  fof(f24,plain,(
% 0.22/0.59    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.59    inference(flattening,[],[f23])).
% 0.22/0.59  fof(f23,plain,(
% 0.22/0.59    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f7])).
% 0.22/0.59  fof(f7,axiom,(
% 0.22/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.60  fof(f1018,plain,(
% 0.22/0.60    ~v1_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = sK1),
% 0.22/0.60    inference(global_subsumption,[],[f50,f988,f997])).
% 0.22/0.60  fof(f997,plain,(
% 0.22/0.60    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2)) | k1_xboole_0 = sK1),
% 0.22/0.60    inference(subsumption_resolution,[],[f987,f549])).
% 0.22/0.60  fof(f549,plain,(
% 0.22/0.60    v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.60    inference(resolution,[],[f544,f69])).
% 0.22/0.60  fof(f544,plain,(
% 0.22/0.60    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.22/0.60    inference(forward_demodulation,[],[f543,f142])).
% 0.22/0.60  fof(f142,plain,(
% 0.22/0.60    sK1 = k2_relat_1(sK2)),
% 0.22/0.60    inference(forward_demodulation,[],[f137,f49])).
% 0.22/0.60  fof(f49,plain,(
% 0.22/0.60    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.60    inference(cnf_transformation,[],[f38])).
% 0.22/0.60  fof(f137,plain,(
% 0.22/0.60    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.22/0.60    inference(resolution,[],[f70,f47])).
% 0.22/0.60  fof(f70,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f30])).
% 0.22/0.60  fof(f30,plain,(
% 0.22/0.60    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.60    inference(ennf_transformation,[],[f13])).
% 0.22/0.60  fof(f13,axiom,(
% 0.22/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.60  fof(f543,plain,(
% 0.22/0.60    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.22/0.60    inference(forward_demodulation,[],[f542,f129])).
% 0.22/0.60  fof(f129,plain,(
% 0.22/0.60    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.60    inference(subsumption_resolution,[],[f128,f93])).
% 0.22/0.60  fof(f128,plain,(
% 0.22/0.60    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.60    inference(subsumption_resolution,[],[f127,f45])).
% 0.22/0.60  fof(f127,plain,(
% 0.22/0.60    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.60    inference(resolution,[],[f58,f48])).
% 0.22/0.60  fof(f48,plain,(
% 0.22/0.60    v2_funct_1(sK2)),
% 0.22/0.60    inference(cnf_transformation,[],[f38])).
% 0.22/0.60  % (8502)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.60  fof(f58,plain,(
% 0.22/0.60    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f26])).
% 0.22/0.60  fof(f26,plain,(
% 0.22/0.60    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.60    inference(flattening,[],[f25])).
% 0.22/0.60  fof(f25,plain,(
% 0.22/0.60    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.60    inference(ennf_transformation,[],[f9])).
% 0.22/0.60  fof(f9,axiom,(
% 0.22/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.60  fof(f542,plain,(
% 0.22/0.60    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))),
% 0.22/0.60    inference(forward_demodulation,[],[f541,f133])).
% 0.22/0.60  fof(f133,plain,(
% 0.22/0.60    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.60    inference(subsumption_resolution,[],[f132,f93])).
% 0.22/0.60  fof(f132,plain,(
% 0.22/0.60    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.60    inference(subsumption_resolution,[],[f131,f45])).
% 0.22/0.60  fof(f131,plain,(
% 0.22/0.60    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.60    inference(resolution,[],[f59,f48])).
% 0.22/0.60  % (8497)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.60  fof(f59,plain,(
% 0.22/0.60    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f26])).
% 0.22/0.60  fof(f541,plain,(
% 0.22/0.60    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))),
% 0.22/0.60    inference(subsumption_resolution,[],[f539,f93])).
% 0.22/0.60  fof(f539,plain,(
% 0.22/0.60    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~v1_relat_1(sK2)),
% 0.22/0.60    inference(resolution,[],[f122,f45])).
% 0.22/0.60  fof(f122,plain,(
% 0.22/0.60    ( ! [X0] : (~v1_funct_1(X0) | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0))))) | ~v1_relat_1(X0)) )),
% 0.22/0.60    inference(subsumption_resolution,[],[f120,f56])).
% 0.22/0.60  fof(f56,plain,(
% 0.22/0.60    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f24])).
% 0.22/0.60  fof(f120,plain,(
% 0.22/0.60    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0))))) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.60    inference(resolution,[],[f55,f57])).
% 0.22/0.60  fof(f55,plain,(
% 0.22/0.60    ( ! [X0] : (~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f22])).
% 0.22/0.60  fof(f22,plain,(
% 0.22/0.60    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.60    inference(flattening,[],[f21])).
% 0.22/0.60  fof(f21,plain,(
% 0.22/0.60    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.60    inference(ennf_transformation,[],[f15])).
% 0.22/0.60  fof(f15,axiom,(
% 0.22/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.22/0.60  fof(f987,plain,(
% 0.22/0.60    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = sK1),
% 0.22/0.60    inference(superposition,[],[f502,f972])).
% 0.22/0.60  fof(f972,plain,(
% 0.22/0.60    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.22/0.60    inference(superposition,[],[f971,f176])).
% 0.22/0.60  fof(f176,plain,(
% 0.22/0.60    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.60    inference(resolution,[],[f71,f47])).
% 0.22/0.60  fof(f971,plain,(
% 0.22/0.60    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 0.22/0.60    inference(subsumption_resolution,[],[f969,f47])).
% 0.22/0.60  fof(f969,plain,(
% 0.22/0.60    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.60    inference(resolution,[],[f73,f46])).
% 0.22/0.60  fof(f46,plain,(
% 0.22/0.60    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.60    inference(cnf_transformation,[],[f38])).
% 0.22/0.60  fof(f73,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.60    inference(cnf_transformation,[],[f44])).
% 0.22/0.60  fof(f502,plain,(
% 0.22/0.60    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.60    inference(forward_demodulation,[],[f135,f142])).
% 0.22/0.60  fof(f135,plain,(
% 0.22/0.60    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.60    inference(forward_demodulation,[],[f134,f129])).
% 0.22/0.60  fof(f134,plain,(
% 0.22/0.60    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.60    inference(superposition,[],[f54,f133])).
% 0.22/0.60  fof(f54,plain,(
% 0.22/0.60    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f22])).
% 0.22/0.60  fof(f988,plain,(
% 0.22/0.60    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK1),
% 0.22/0.60    inference(superposition,[],[f544,f972])).
% 0.22/0.60  fof(f50,plain,(
% 0.22/0.60    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.60    inference(cnf_transformation,[],[f38])).
% 0.22/0.60  fof(f114,plain,(
% 0.22/0.60    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | sK2 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.60    inference(resolution,[],[f63,f90])).
% 0.22/0.60  fof(f90,plain,(
% 0.22/0.60    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.22/0.60    inference(resolution,[],[f64,f47])).
% 0.22/0.60  fof(f45,plain,(
% 0.22/0.60    v1_funct_1(sK2)),
% 0.22/0.60    inference(cnf_transformation,[],[f38])).
% 0.22/0.60  fof(f1277,plain,(
% 0.22/0.60    ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)),
% 0.22/0.60    inference(forward_demodulation,[],[f1276,f1175])).
% 0.22/0.60  fof(f1175,plain,(
% 0.22/0.60    k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 0.22/0.60    inference(forward_demodulation,[],[f1060,f1049])).
% 0.22/0.60  fof(f1060,plain,(
% 0.22/0.60    k1_xboole_0 = k2_funct_1(sK2)),
% 0.22/0.60    inference(forward_demodulation,[],[f1059,f83])).
% 0.22/0.60  fof(f1059,plain,(
% 0.22/0.60    k2_funct_1(sK2) = k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))),
% 0.22/0.60    inference(subsumption_resolution,[],[f1058,f89])).
% 0.22/0.60  fof(f1058,plain,(
% 0.22/0.60    ~r1_tarski(k1_xboole_0,k2_funct_1(sK2)) | k2_funct_1(sK2) = k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))),
% 0.22/0.60    inference(forward_demodulation,[],[f1042,f83])).
% 0.22/0.60  fof(f1042,plain,(
% 0.22/0.60    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)),k2_funct_1(sK2)) | k2_funct_1(sK2) = k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))),
% 0.22/0.60    inference(superposition,[],[f562,f1021])).
% 0.22/0.60  fof(f562,plain,(
% 0.22/0.60    ~r1_tarski(k2_zfmisc_1(sK1,k1_relat_1(sK2)),k2_funct_1(sK2)) | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2))),
% 0.22/0.60    inference(resolution,[],[f550,f63])).
% 0.22/0.60  fof(f550,plain,(
% 0.22/0.60    r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2)))),
% 0.22/0.60    inference(resolution,[],[f544,f64])).
% 0.22/0.60  fof(f1276,plain,(
% 0.22/0.60    ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)),
% 0.22/0.60    inference(forward_demodulation,[],[f1275,f1049])).
% 0.22/0.60  fof(f1275,plain,(
% 0.22/0.60    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.60    inference(forward_demodulation,[],[f1274,f1175])).
% 0.22/0.60  fof(f1274,plain,(
% 0.22/0.60    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.60    inference(forward_demodulation,[],[f1273,f1049])).
% 0.22/0.60  fof(f1273,plain,(
% 0.22/0.60    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.60    inference(subsumption_resolution,[],[f1272,f51])).
% 1.77/0.60  fof(f1272,plain,(
% 1.77/0.60    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 1.77/0.60    inference(forward_demodulation,[],[f1271,f1175])).
% 1.77/0.60  fof(f1271,plain,(
% 1.77/0.60    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 1.77/0.60    inference(forward_demodulation,[],[f1045,f1049])).
% 1.77/0.60  fof(f1045,plain,(
% 1.77/0.60    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 1.77/0.60    inference(forward_demodulation,[],[f1025,f83])).
% 1.77/0.60  fof(f1025,plain,(
% 1.77/0.60    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~v1_funct_1(k2_funct_1(sK2))),
% 1.77/0.60    inference(superposition,[],[f50,f1021])).
% 1.77/0.60  % SZS output end Proof for theBenchmark
% 1.77/0.60  % (8501)------------------------------
% 1.77/0.60  % (8501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.60  % (8501)Termination reason: Refutation
% 1.77/0.60  
% 1.77/0.60  % (8501)Memory used [KB]: 6780
% 1.77/0.60  % (8501)Time elapsed: 0.174 s
% 1.77/0.60  % (8501)------------------------------
% 1.77/0.60  % (8501)------------------------------
% 1.77/0.60  % (8487)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.77/0.60  % (8490)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.77/0.60  % (8479)Success in time 0.235 s
%------------------------------------------------------------------------------
