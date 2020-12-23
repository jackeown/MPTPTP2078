%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:07 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  106 (1297 expanded)
%              Number of leaves         :   11 ( 240 expanded)
%              Depth                    :   33
%              Number of atoms          :  329 (7274 expanded)
%              Number of equality atoms :  136 (1746 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f454,plain,(
    $false ),
    inference(subsumption_resolution,[],[f446,f104])).

fof(f104,plain,(
    ! [X0,X1] : r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f76,f41])).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f75])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f446,plain,(
    ~ r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f415,f437])).

fof(f437,plain,(
    k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f436,f68])).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f436,plain,(
    sK2 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f435,f335])).

fof(f335,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f317,f106])).

fof(f106,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f76,f39])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f317,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f36,f313])).

fof(f313,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f312,f243])).

fof(f243,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f236,f111])).

fof(f111,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f56,f39])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f236,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f231,f39])).

fof(f231,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f62,f38])).

fof(f38,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f312,plain,
    ( sK0 != k1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f311])).

fof(f311,plain,
    ( sK0 != k1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f310,f238])).

fof(f238,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f235,f110])).

fof(f110,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f56,f35])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f235,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f230,f35])).

fof(f230,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f62,f34])).

fof(f34,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f310,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f309,f87])).

fof(f87,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f55,f39])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f309,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f308,f33])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f308,plain,
    ( ~ v1_funct_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f307,f86])).

fof(f86,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f55,f35])).

fof(f307,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f306,f37])).

fof(f37,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f306,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f305])).

fof(f305,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f304])).

fof(f304,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = sK3
    | k1_xboole_0 = sK1
    | sK2 = sK3 ),
    inference(superposition,[],[f43,f282])).

fof(f282,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | k1_xboole_0 = sK1
    | sK2 = sK3 ),
    inference(resolution,[],[f279,f32])).

fof(f32,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f279,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f278])).

fof(f278,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | sK2 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f271,f243])).

fof(f271,plain,
    ( r2_hidden(sK4(sK2,sK3),k1_relat_1(sK2))
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f270,f243])).

fof(f270,plain,
    ( sK0 != k1_relat_1(sK2)
    | r2_hidden(sK4(sK2,sK3),k1_relat_1(sK2))
    | sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f269,f238])).

fof(f269,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK2)
    | r2_hidden(sK4(sK2,sK3),k1_relat_1(sK2))
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f268,f87])).

fof(f268,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | r2_hidden(sK4(sK2,sK3),k1_relat_1(sK2))
    | sK2 = sK3 ),
    inference(resolution,[],[f265,f37])).

fof(f265,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | r2_hidden(sK4(X0,sK3),k1_relat_1(X0))
      | sK3 = X0 ) ),
    inference(subsumption_resolution,[],[f263,f86])).

fof(f263,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK3)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | r2_hidden(sK4(X0,sK3),k1_relat_1(X0))
      | sK3 = X0 ) ),
    inference(resolution,[],[f42,f33])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f36,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f435,plain,(
    sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f434,f149])).

fof(f149,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(duplicate_literal_removal,[],[f143])).

fof(f143,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,X0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f119,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f119,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(k1_xboole_0,X0),X1)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f98,f41])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r2_hidden(sK5(X0,X2),X1)
      | r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f45,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f434,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f358,f68])).

fof(f358,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f137,f335])).

fof(f137,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f135,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f135,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f121,f51])).

fof(f121,plain,(
    ! [X3] :
      ( r2_hidden(sK5(sK2,X3),k2_zfmisc_1(sK0,sK1))
      | r1_tarski(sK2,X3) ) ),
    inference(resolution,[],[f98,f39])).

fof(f415,plain,(
    ~ r2_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f338,f396])).

fof(f396,plain,(
    k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f395,f68])).

fof(f395,plain,(
    sK3 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f394,f335])).

fof(f394,plain,(
    sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f393,f149])).

fof(f393,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f352,f68])).

fof(f352,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f129,f335])).

fof(f129,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f127,f48])).

fof(f127,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f120,f51])).

fof(f120,plain,(
    ! [X2] :
      ( r2_hidden(sK5(sK3,X2),k2_zfmisc_1(sK0,sK1))
      | r1_tarski(sK3,X2) ) ),
    inference(resolution,[],[f98,f35])).

fof(f338,plain,(
    ~ r2_relset_1(sK0,k1_xboole_0,sK2,sK3) ),
    inference(backward_demodulation,[],[f36,f335])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:47:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (25231)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (25239)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (25237)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (25247)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (25239)Refutation not found, incomplete strategy% (25239)------------------------------
% 0.21/0.53  % (25239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (25239)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (25239)Memory used [KB]: 10746
% 0.21/0.53  % (25239)Time elapsed: 0.099 s
% 0.21/0.53  % (25239)------------------------------
% 0.21/0.53  % (25239)------------------------------
% 1.31/0.54  % (25235)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.31/0.54  % (25238)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.31/0.54  % (25236)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.31/0.54  % (25246)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.31/0.54  % (25257)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.31/0.55  % (25234)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.31/0.55  % (25243)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.55  % (25260)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.31/0.55  % (25232)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.31/0.55  % (25259)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.55  % (25255)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.41/0.55  % (25258)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.55  % (25252)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.41/0.55  % (25254)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.55  % (25251)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.56  % (25249)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.56  % (25250)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.56  % (25245)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.41/0.56  % (25256)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.41/0.56  % (25244)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.41/0.56  % (25242)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.41/0.57  % (25237)Refutation found. Thanks to Tanya!
% 1.41/0.57  % SZS status Theorem for theBenchmark
% 1.41/0.57  % SZS output start Proof for theBenchmark
% 1.41/0.57  fof(f454,plain,(
% 1.41/0.57    $false),
% 1.41/0.57    inference(subsumption_resolution,[],[f446,f104])).
% 1.41/0.57  fof(f104,plain,(
% 1.41/0.57    ( ! [X0,X1] : (r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0)) )),
% 1.41/0.57    inference(resolution,[],[f76,f41])).
% 1.41/0.57  fof(f41,plain,(
% 1.41/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.41/0.57    inference(cnf_transformation,[],[f7])).
% 1.41/0.57  fof(f7,axiom,(
% 1.41/0.57    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.41/0.57  fof(f76,plain,(
% 1.41/0.57    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.41/0.57    inference(duplicate_literal_removal,[],[f75])).
% 1.41/0.57  fof(f75,plain,(
% 1.41/0.57    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.41/0.57    inference(equality_resolution,[],[f64])).
% 1.41/0.57  fof(f64,plain,(
% 1.41/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f31])).
% 1.41/0.57  fof(f31,plain,(
% 1.41/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.57    inference(flattening,[],[f30])).
% 1.41/0.57  fof(f30,plain,(
% 1.41/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.41/0.57    inference(ennf_transformation,[],[f12])).
% 1.41/0.57  fof(f12,axiom,(
% 1.41/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.41/0.57  fof(f446,plain,(
% 1.41/0.57    ~r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.41/0.57    inference(backward_demodulation,[],[f415,f437])).
% 1.41/0.57  fof(f437,plain,(
% 1.41/0.57    k1_xboole_0 = sK2),
% 1.41/0.57    inference(forward_demodulation,[],[f436,f68])).
% 1.41/0.57  fof(f68,plain,(
% 1.41/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.41/0.57    inference(equality_resolution,[],[f54])).
% 1.41/0.57  fof(f54,plain,(
% 1.41/0.57    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f5])).
% 1.41/0.57  fof(f5,axiom,(
% 1.41/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.41/0.57  fof(f436,plain,(
% 1.41/0.57    sK2 = k2_zfmisc_1(sK0,k1_xboole_0)),
% 1.41/0.57    inference(forward_demodulation,[],[f435,f335])).
% 1.41/0.57  fof(f335,plain,(
% 1.41/0.57    k1_xboole_0 = sK1),
% 1.41/0.57    inference(subsumption_resolution,[],[f317,f106])).
% 1.41/0.57  fof(f106,plain,(
% 1.41/0.57    r2_relset_1(sK0,sK1,sK2,sK2)),
% 1.41/0.57    inference(resolution,[],[f76,f39])).
% 1.41/0.57  fof(f39,plain,(
% 1.41/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.41/0.57    inference(cnf_transformation,[],[f18])).
% 1.41/0.57  fof(f18,plain,(
% 1.41/0.57    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.41/0.57    inference(flattening,[],[f17])).
% 1.41/0.57  fof(f17,plain,(
% 1.41/0.57    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.41/0.57    inference(ennf_transformation,[],[f15])).
% 1.41/0.57  fof(f15,negated_conjecture,(
% 1.41/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.41/0.57    inference(negated_conjecture,[],[f14])).
% 1.41/0.57  fof(f14,conjecture,(
% 1.41/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).
% 1.41/0.57  fof(f317,plain,(
% 1.41/0.57    ~r2_relset_1(sK0,sK1,sK2,sK2) | k1_xboole_0 = sK1),
% 1.41/0.57    inference(superposition,[],[f36,f313])).
% 1.41/0.57  fof(f313,plain,(
% 1.41/0.57    sK2 = sK3 | k1_xboole_0 = sK1),
% 1.41/0.57    inference(subsumption_resolution,[],[f312,f243])).
% 1.41/0.57  fof(f243,plain,(
% 1.41/0.57    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 1.41/0.57    inference(superposition,[],[f236,f111])).
% 1.41/0.57  fof(f111,plain,(
% 1.41/0.57    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 1.41/0.57    inference(resolution,[],[f56,f39])).
% 1.41/0.57  fof(f56,plain,(
% 1.41/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f25])).
% 1.41/0.57  fof(f25,plain,(
% 1.41/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.57    inference(ennf_transformation,[],[f11])).
% 1.41/0.57  fof(f11,axiom,(
% 1.41/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.41/0.57  fof(f236,plain,(
% 1.41/0.57    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 1.41/0.57    inference(subsumption_resolution,[],[f231,f39])).
% 1.41/0.57  fof(f231,plain,(
% 1.41/0.57    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.41/0.57    inference(resolution,[],[f62,f38])).
% 1.41/0.57  fof(f38,plain,(
% 1.41/0.57    v1_funct_2(sK2,sK0,sK1)),
% 1.41/0.57    inference(cnf_transformation,[],[f18])).
% 1.41/0.57  fof(f62,plain,(
% 1.41/0.57    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.57    inference(cnf_transformation,[],[f27])).
% 1.41/0.57  fof(f27,plain,(
% 1.41/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.57    inference(flattening,[],[f26])).
% 1.41/0.57  fof(f26,plain,(
% 1.41/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.57    inference(ennf_transformation,[],[f13])).
% 1.41/0.57  fof(f13,axiom,(
% 1.41/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.41/0.57  fof(f312,plain,(
% 1.41/0.57    sK0 != k1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1),
% 1.41/0.57    inference(duplicate_literal_removal,[],[f311])).
% 1.41/0.57  fof(f311,plain,(
% 1.41/0.57    sK0 != k1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 1.41/0.57    inference(superposition,[],[f310,f238])).
% 1.41/0.57  fof(f238,plain,(
% 1.41/0.57    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 1.41/0.57    inference(superposition,[],[f235,f110])).
% 1.41/0.57  fof(f110,plain,(
% 1.41/0.57    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.41/0.57    inference(resolution,[],[f56,f35])).
% 1.41/0.57  fof(f35,plain,(
% 1.41/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.41/0.57    inference(cnf_transformation,[],[f18])).
% 1.41/0.57  fof(f235,plain,(
% 1.41/0.57    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 1.41/0.57    inference(subsumption_resolution,[],[f230,f35])).
% 1.41/0.57  fof(f230,plain,(
% 1.41/0.57    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.41/0.57    inference(resolution,[],[f62,f34])).
% 1.41/0.57  fof(f34,plain,(
% 1.41/0.57    v1_funct_2(sK3,sK0,sK1)),
% 1.41/0.57    inference(cnf_transformation,[],[f18])).
% 1.41/0.57  fof(f310,plain,(
% 1.41/0.57    k1_relat_1(sK3) != k1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1),
% 1.41/0.57    inference(subsumption_resolution,[],[f309,f87])).
% 1.41/0.57  fof(f87,plain,(
% 1.41/0.57    v1_relat_1(sK2)),
% 1.41/0.57    inference(resolution,[],[f55,f39])).
% 1.41/0.57  fof(f55,plain,(
% 1.41/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f24])).
% 1.41/0.57  fof(f24,plain,(
% 1.41/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.57    inference(ennf_transformation,[],[f10])).
% 1.41/0.57  fof(f10,axiom,(
% 1.41/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.41/0.57  fof(f309,plain,(
% 1.41/0.57    k1_relat_1(sK3) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1),
% 1.41/0.57    inference(subsumption_resolution,[],[f308,f33])).
% 1.41/0.57  fof(f33,plain,(
% 1.41/0.57    v1_funct_1(sK3)),
% 1.41/0.57    inference(cnf_transformation,[],[f18])).
% 1.41/0.57  fof(f308,plain,(
% 1.41/0.57    ~v1_funct_1(sK3) | k1_relat_1(sK3) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1),
% 1.41/0.57    inference(subsumption_resolution,[],[f307,f86])).
% 1.41/0.57  fof(f86,plain,(
% 1.41/0.57    v1_relat_1(sK3)),
% 1.41/0.57    inference(resolution,[],[f55,f35])).
% 1.41/0.57  fof(f307,plain,(
% 1.41/0.57    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | k1_relat_1(sK3) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1),
% 1.41/0.57    inference(subsumption_resolution,[],[f306,f37])).
% 1.41/0.57  fof(f37,plain,(
% 1.41/0.57    v1_funct_1(sK2)),
% 1.41/0.57    inference(cnf_transformation,[],[f18])).
% 1.41/0.57  fof(f306,plain,(
% 1.41/0.57    ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | k1_relat_1(sK3) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1),
% 1.41/0.57    inference(trivial_inequality_removal,[],[f305])).
% 1.41/0.57  fof(f305,plain,(
% 1.41/0.57    k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | k1_relat_1(sK3) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1),
% 1.41/0.57    inference(duplicate_literal_removal,[],[f304])).
% 1.41/0.57  fof(f304,plain,(
% 1.41/0.57    k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | k1_relat_1(sK3) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | sK2 = sK3 | k1_xboole_0 = sK1 | sK2 = sK3),
% 1.41/0.57    inference(superposition,[],[f43,f282])).
% 1.41/0.57  fof(f282,plain,(
% 1.41/0.57    k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) | k1_xboole_0 = sK1 | sK2 = sK3),
% 1.41/0.57    inference(resolution,[],[f279,f32])).
% 1.41/0.57  fof(f32,plain,(
% 1.41/0.57    ( ! [X4] : (~r2_hidden(X4,sK0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f18])).
% 1.41/0.57  fof(f279,plain,(
% 1.41/0.57    r2_hidden(sK4(sK2,sK3),sK0) | sK2 = sK3 | k1_xboole_0 = sK1),
% 1.41/0.57    inference(duplicate_literal_removal,[],[f278])).
% 1.41/0.57  fof(f278,plain,(
% 1.41/0.57    r2_hidden(sK4(sK2,sK3),sK0) | sK2 = sK3 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 1.41/0.57    inference(superposition,[],[f271,f243])).
% 1.41/0.57  fof(f271,plain,(
% 1.41/0.57    r2_hidden(sK4(sK2,sK3),k1_relat_1(sK2)) | sK2 = sK3 | k1_xboole_0 = sK1),
% 1.41/0.57    inference(subsumption_resolution,[],[f270,f243])).
% 1.41/0.57  fof(f270,plain,(
% 1.41/0.57    sK0 != k1_relat_1(sK2) | r2_hidden(sK4(sK2,sK3),k1_relat_1(sK2)) | sK2 = sK3 | k1_xboole_0 = sK1),
% 1.41/0.57    inference(superposition,[],[f269,f238])).
% 1.41/0.57  fof(f269,plain,(
% 1.41/0.57    k1_relat_1(sK3) != k1_relat_1(sK2) | r2_hidden(sK4(sK2,sK3),k1_relat_1(sK2)) | sK2 = sK3),
% 1.41/0.57    inference(subsumption_resolution,[],[f268,f87])).
% 1.41/0.57  fof(f268,plain,(
% 1.41/0.57    ~v1_relat_1(sK2) | k1_relat_1(sK3) != k1_relat_1(sK2) | r2_hidden(sK4(sK2,sK3),k1_relat_1(sK2)) | sK2 = sK3),
% 1.41/0.57    inference(resolution,[],[f265,f37])).
% 1.41/0.57  fof(f265,plain,(
% 1.41/0.57    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) != k1_relat_1(sK3) | r2_hidden(sK4(X0,sK3),k1_relat_1(X0)) | sK3 = X0) )),
% 1.41/0.57    inference(subsumption_resolution,[],[f263,f86])).
% 1.41/0.57  fof(f263,plain,(
% 1.41/0.57    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(sK3) | ~v1_relat_1(X0) | k1_relat_1(X0) != k1_relat_1(sK3) | r2_hidden(sK4(X0,sK3),k1_relat_1(X0)) | sK3 = X0) )),
% 1.41/0.57    inference(resolution,[],[f42,f33])).
% 1.41/0.57  fof(f42,plain,(
% 1.41/0.57    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(X0) != k1_relat_1(X1) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | X0 = X1) )),
% 1.41/0.57    inference(cnf_transformation,[],[f20])).
% 1.41/0.57  fof(f20,plain,(
% 1.41/0.57    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.41/0.57    inference(flattening,[],[f19])).
% 1.41/0.57  fof(f19,plain,(
% 1.41/0.57    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.41/0.57    inference(ennf_transformation,[],[f9])).
% 1.41/0.57  fof(f9,axiom,(
% 1.41/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 1.41/0.57  fof(f43,plain,(
% 1.41/0.57    ( ! [X0,X1] : (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X0) | X0 = X1) )),
% 1.41/0.57    inference(cnf_transformation,[],[f20])).
% 1.41/0.57  fof(f36,plain,(
% 1.41/0.57    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 1.41/0.57    inference(cnf_transformation,[],[f18])).
% 1.41/0.57  fof(f435,plain,(
% 1.41/0.57    sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.41/0.57    inference(subsumption_resolution,[],[f434,f149])).
% 1.41/0.57  fof(f149,plain,(
% 1.41/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.41/0.57    inference(duplicate_literal_removal,[],[f143])).
% 1.41/0.57  fof(f143,plain,(
% 1.41/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0) | r1_tarski(k1_xboole_0,X0)) )),
% 1.41/0.57    inference(resolution,[],[f119,f51])).
% 1.41/0.57  fof(f51,plain,(
% 1.41/0.57    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f23])).
% 1.41/0.57  fof(f23,plain,(
% 1.41/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.41/0.57    inference(ennf_transformation,[],[f2])).
% 1.41/0.57  fof(f2,axiom,(
% 1.41/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.41/0.57  fof(f119,plain,(
% 1.41/0.57    ( ! [X0,X1] : (r2_hidden(sK5(k1_xboole_0,X0),X1) | r1_tarski(k1_xboole_0,X0)) )),
% 1.41/0.57    inference(resolution,[],[f98,f41])).
% 1.41/0.57  fof(f98,plain,(
% 1.41/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(sK5(X0,X2),X1) | r1_tarski(X0,X2)) )),
% 1.41/0.57    inference(resolution,[],[f45,f50])).
% 1.41/0.57  fof(f50,plain,(
% 1.41/0.57    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f23])).
% 1.41/0.57  fof(f45,plain,(
% 1.41/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(X2,X0)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f22])).
% 1.41/0.57  fof(f22,plain,(
% 1.41/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.41/0.57    inference(ennf_transformation,[],[f6])).
% 1.41/0.57  fof(f6,axiom,(
% 1.41/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.41/0.57  fof(f434,plain,(
% 1.41/0.57    ~r1_tarski(k1_xboole_0,sK2) | sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.41/0.57    inference(forward_demodulation,[],[f358,f68])).
% 1.41/0.57  fof(f358,plain,(
% 1.41/0.57    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2) | sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.41/0.57    inference(backward_demodulation,[],[f137,f335])).
% 1.41/0.57  fof(f137,plain,(
% 1.41/0.57    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.41/0.57    inference(resolution,[],[f135,f48])).
% 1.41/0.57  fof(f48,plain,(
% 1.41/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.41/0.57    inference(cnf_transformation,[],[f4])).
% 1.41/0.57  fof(f4,axiom,(
% 1.41/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.41/0.57  fof(f135,plain,(
% 1.41/0.57    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.41/0.57    inference(duplicate_literal_removal,[],[f130])).
% 1.41/0.57  fof(f130,plain,(
% 1.41/0.57    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.41/0.57    inference(resolution,[],[f121,f51])).
% 1.41/0.57  fof(f121,plain,(
% 1.41/0.57    ( ! [X3] : (r2_hidden(sK5(sK2,X3),k2_zfmisc_1(sK0,sK1)) | r1_tarski(sK2,X3)) )),
% 1.41/0.57    inference(resolution,[],[f98,f39])).
% 1.41/0.57  fof(f415,plain,(
% 1.41/0.57    ~r2_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0)),
% 1.41/0.57    inference(backward_demodulation,[],[f338,f396])).
% 1.41/0.57  fof(f396,plain,(
% 1.41/0.57    k1_xboole_0 = sK3),
% 1.41/0.57    inference(forward_demodulation,[],[f395,f68])).
% 1.41/0.57  fof(f395,plain,(
% 1.41/0.57    sK3 = k2_zfmisc_1(sK0,k1_xboole_0)),
% 1.41/0.57    inference(forward_demodulation,[],[f394,f335])).
% 1.41/0.57  fof(f394,plain,(
% 1.41/0.57    sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.41/0.57    inference(subsumption_resolution,[],[f393,f149])).
% 1.41/0.57  fof(f393,plain,(
% 1.41/0.57    ~r1_tarski(k1_xboole_0,sK3) | sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.41/0.57    inference(forward_demodulation,[],[f352,f68])).
% 1.41/0.57  fof(f352,plain,(
% 1.41/0.57    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3) | sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.41/0.57    inference(backward_demodulation,[],[f129,f335])).
% 1.41/0.57  fof(f129,plain,(
% 1.41/0.57    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) | sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.41/0.57    inference(resolution,[],[f127,f48])).
% 1.41/0.57  fof(f127,plain,(
% 1.41/0.57    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.41/0.57    inference(duplicate_literal_removal,[],[f122])).
% 1.41/0.57  fof(f122,plain,(
% 1.41/0.57    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.41/0.57    inference(resolution,[],[f120,f51])).
% 1.41/0.57  fof(f120,plain,(
% 1.41/0.57    ( ! [X2] : (r2_hidden(sK5(sK3,X2),k2_zfmisc_1(sK0,sK1)) | r1_tarski(sK3,X2)) )),
% 1.41/0.57    inference(resolution,[],[f98,f35])).
% 1.41/0.57  fof(f338,plain,(
% 1.41/0.57    ~r2_relset_1(sK0,k1_xboole_0,sK2,sK3)),
% 1.41/0.57    inference(backward_demodulation,[],[f36,f335])).
% 1.41/0.57  % SZS output end Proof for theBenchmark
% 1.41/0.57  % (25237)------------------------------
% 1.41/0.57  % (25237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.57  % (25237)Termination reason: Refutation
% 1.41/0.57  
% 1.41/0.57  % (25237)Memory used [KB]: 6524
% 1.41/0.57  % (25237)Time elapsed: 0.133 s
% 1.41/0.57  % (25237)------------------------------
% 1.41/0.57  % (25237)------------------------------
% 1.41/0.57  % (25230)Success in time 0.205 s
%------------------------------------------------------------------------------
