%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0972+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  112 (35382 expanded)
%              Number of leaves         :    6 (6377 expanded)
%              Depth                    :   38
%              Number of atoms          :  324 (205112 expanded)
%              Number of equality atoms :  162 (49386 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f262,plain,(
    $false ),
    inference(subsumption_resolution,[],[f256,f196])).

fof(f196,plain,(
    r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) ),
    inference(backward_demodulation,[],[f134,f186])).

fof(f186,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f185,f163])).

fof(f163,plain,
    ( r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f132,f137])).

fof(f137,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f135,f127])).

fof(f127,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f21,f125])).

fof(f125,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f109,f60])).

fof(f60,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f25,f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( r2_hidden(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

fof(f109,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f22,f102])).

fof(f102,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f101,f87])).

fof(f87,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f52,f58])).

fof(f58,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f25,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f52,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f51,f25])).

fof(f51,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f24,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f24,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f101,plain,
    ( sK0 != k1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,
    ( sK0 != k1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f99,f75])).

fof(f75,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f50,f54])).

fof(f54,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f21,f36])).

fof(f50,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f49,f21])).

fof(f49,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f20,f35])).

fof(f20,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f99,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f98])).

fof(f98,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1
    | sK2 = sK3 ),
    inference(superposition,[],[f81,f93])).

fof(f93,plain,
    ( k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2))
    | k1_xboole_0 = sK1
    | sK2 = sK3 ),
    inference(resolution,[],[f90,f18])).

fof(f18,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f90,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f89,f87])).

fof(f89,plain,
    ( sK0 != k1_relat_1(sK2)
    | r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f69,f75])).

fof(f69,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK2)
    | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f68,f53])).

fof(f53,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f21,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f68,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f66,f57])).

fof(f57,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f25,f37])).

fof(f66,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | sK2 = sK3 ),
    inference(resolution,[],[f45,f23])).

fof(f23,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK3)
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | r2_hidden(sK4(sK3,X0),k1_relat_1(sK3))
      | sK3 = X0 ) ),
    inference(resolution,[],[f19,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
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
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(f19,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f81,plain,
    ( k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f80,f53])).

fof(f80,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f78,f57])).

fof(f78,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3 ),
    inference(resolution,[],[f46,f23])).

fof(f46,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(sK3)
      | k1_relat_1(X1) != k1_relat_1(sK3)
      | k1_funct_1(sK3,sK4(sK3,X1)) != k1_funct_1(X1,sK4(sK3,X1))
      | sK3 = X1 ) ),
    inference(resolution,[],[f19,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f22,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f21,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f135,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f126,f41])).

fof(f41,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f126,plain,(
    v1_funct_2(sK3,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f20,f125])).

fof(f132,plain,(
    r2_relset_1(sK0,k1_xboole_0,sK3,sK3) ),
    inference(backward_demodulation,[],[f56,f125])).

fof(f56,plain,(
    r2_relset_1(sK0,sK1,sK3,sK3) ),
    inference(resolution,[],[f21,f44])).

fof(f185,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f184])).

fof(f184,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f161,f140])).

fof(f140,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f138,f130])).

fof(f130,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f25,f125])).

fof(f138,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f129,f41])).

fof(f129,plain,(
    v1_funct_2(sK2,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f24,f125])).

fof(f161,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f128,f137])).

fof(f128,plain,(
    ~ r2_relset_1(sK0,k1_xboole_0,sK2,sK3) ),
    inference(backward_demodulation,[],[f22,f125])).

fof(f134,plain,(
    r2_relset_1(sK0,k1_xboole_0,sK2,sK2) ),
    inference(backward_demodulation,[],[f60,f125])).

fof(f256,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK2) ),
    inference(backward_demodulation,[],[f190,f251])).

fof(f251,plain,(
    sK2 = sK3 ),
    inference(subsumption_resolution,[],[f250,f225])).

fof(f225,plain,
    ( k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3 ),
    inference(trivial_inequality_removal,[],[f220])).

fof(f220,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3 ),
    inference(backward_demodulation,[],[f206,f216])).

fof(f216,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f195,f215])).

fof(f215,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f212,f192])).

fof(f192,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f130,f186])).

fof(f212,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f191,f39])).

fof(f39,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f191,plain,(
    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f129,f186])).

fof(f195,plain,(
    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f133,f186])).

fof(f133,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f58,f125])).

fof(f206,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3 ),
    inference(backward_demodulation,[],[f81,f201])).

fof(f201,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f193,f200])).

fof(f200,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(subsumption_resolution,[],[f197,f189])).

fof(f189,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f127,f186])).

fof(f197,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f188,f39])).

fof(f188,plain,(
    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f126,f186])).

fof(f193,plain,(
    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f131,f186])).

fof(f131,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f54,f125])).

fof(f250,plain,
    ( sK2 = sK3
    | k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2)) ),
    inference(resolution,[],[f223,f187])).

fof(f187,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(backward_demodulation,[],[f18,f186])).

fof(f223,plain,
    ( r2_hidden(sK4(sK3,sK2),k1_xboole_0)
    | sK2 = sK3 ),
    inference(trivial_inequality_removal,[],[f222])).

fof(f222,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK4(sK3,sK2),k1_xboole_0)
    | sK2 = sK3 ),
    inference(backward_demodulation,[],[f211,f216])).

fof(f211,plain,
    ( r2_hidden(sK4(sK3,sK2),k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(sK2)
    | sK2 = sK3 ),
    inference(forward_demodulation,[],[f204,f201])).

fof(f204,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | sK2 = sK3 ),
    inference(backward_demodulation,[],[f69,f201])).

fof(f190,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK3) ),
    inference(backward_demodulation,[],[f128,f186])).

%------------------------------------------------------------------------------
