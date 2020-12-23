%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 422 expanded)
%              Number of leaves         :   16 ( 154 expanded)
%              Depth                    :   19
%              Number of atoms          :  355 (3083 expanded)
%              Number of equality atoms :   57 ( 420 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f281,plain,(
    $false ),
    inference(subsumption_resolution,[],[f239,f53])).

fof(f53,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f239,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f45,f238])).

fof(f238,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f236,f156])).

fof(f156,plain,(
    k1_relat_1(sK2) != k10_relat_1(sK2,sK0) ),
    inference(superposition,[],[f52,f136])).

fof(f136,plain,(
    k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,sK0) ),
    inference(backward_demodulation,[],[f125,f131])).

fof(f131,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(unit_resulting_resolution,[],[f117,f113,f116,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f116,plain,(
    v1_partfun1(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f45,f46,f47,f48,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v5_relat_1(sK2,sK0)
    & v1_relat_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f40,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
                & v1_funct_1(X2)
                & v5_relat_1(X2,X0)
                & v1_relat_1(X2) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
              & v1_funct_1(X2)
              & v5_relat_1(X2,sK0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_2(X1,sK0,sK0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
            & v1_funct_1(X2)
            & v5_relat_1(X2,sK0)
            & v1_relat_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v1_funct_2(X1,sK0,sK0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,sK1))
          & v1_funct_1(X2)
          & v5_relat_1(X2,sK0)
          & v1_relat_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,sK1))
        & v1_funct_1(X2)
        & v5_relat_1(X2,sK0)
        & v1_relat_1(X2) )
   => ( k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v5_relat_1(sK2,sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
              & v1_funct_1(X2)
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
              & v1_funct_1(X2)
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X1,X0,X0)
              & v1_funct_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v5_relat_1(X2,X0)
                  & v1_relat_1(X2) )
               => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v5_relat_1(X2,X0)
                & v1_relat_1(X2) )
             => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t200_funct_2)).

fof(f47,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f46,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f113,plain,(
    v4_relat_1(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f48,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f117,plain,(
    v1_relat_1(sK1) ),
    inference(unit_resulting_resolution,[],[f59,f48,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f59,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f125,plain,(
    k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f49,f117,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f49,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f52,plain,(
    k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f236,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f229,f219])).

fof(f219,plain,(
    ! [X0] : k8_relset_1(k1_relat_1(sK2),sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(unit_resulting_resolution,[],[f217,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f217,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))) ),
    inference(duplicate_literal_removal,[],[f214])).

fof(f214,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))) ),
    inference(resolution,[],[f213,f110])).

fof(f110,plain,(
    ! [X8] :
      ( ~ r2_hidden(k1_funct_1(sK2,sK3(k1_relat_1(sK2),X8,sK2)),X8)
      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X8))) ) ),
    inference(subsumption_resolution,[],[f106,f49])).

fof(f106,plain,(
    ! [X8] :
      ( ~ r2_hidden(k1_funct_1(sK2,sK3(k1_relat_1(sK2),X8,sK2)),X8)
      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X8)))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f51,f80])).

fof(f80,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k1_funct_1(X2,sK3(k1_relat_1(X2),X1,X2)),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK3(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK3(X0,X1,X2)),X1)
        & r2_hidden(sK3(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK3(X0,X1,X2)),X1)
        & r2_hidden(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f213,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,sK3(k1_relat_1(sK2),X0,sK2)),sK0)
      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) ) ),
    inference(resolution,[],[f185,f50])).

fof(f50,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f185,plain,(
    ! [X2,X3] :
      ( ~ v5_relat_1(sK2,X3)
      | r2_hidden(k1_funct_1(sK2,sK3(k1_relat_1(sK2),X2,sK2)),X3)
      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X2))) ) ),
    inference(subsumption_resolution,[],[f184,f49])).

fof(f184,plain,(
    ! [X2,X3] :
      ( r2_hidden(k1_funct_1(sK2,sK3(k1_relat_1(sK2),X2,sK2)),X3)
      | ~ v5_relat_1(sK2,X3)
      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X2)))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f181,f51])).

fof(f181,plain,(
    ! [X2,X3] :
      ( r2_hidden(k1_funct_1(sK2,sK3(k1_relat_1(sK2),X2,sK2)),X3)
      | ~ v5_relat_1(sK2,X3)
      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X2)))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f109,f81])).

fof(f81,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK3(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f109,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_relat_1(sK2))
      | r2_hidden(k1_funct_1(sK2,X4),X5)
      | ~ v5_relat_1(sK2,X5) ) ),
    inference(subsumption_resolution,[],[f104,f49])).

fof(f104,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_relat_1(sK2))
      | r2_hidden(k1_funct_1(sK2,X4),X5)
      | ~ v5_relat_1(sK2,X5)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f51,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(f229,plain,
    ( k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),sK0,sK2,sK0)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f224,f202])).

fof(f202,plain,(
    v1_funct_2(sK2,k1_relat_1(sK2),sK0) ),
    inference(duplicate_literal_removal,[],[f200])).

fof(f200,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK0)
    | v1_funct_2(sK2,k1_relat_1(sK2),sK0) ),
    inference(resolution,[],[f198,f111])).

fof(f111,plain,(
    ! [X9] :
      ( ~ r2_hidden(k1_funct_1(sK2,sK3(k1_relat_1(sK2),X9,sK2)),X9)
      | v1_funct_2(sK2,k1_relat_1(sK2),X9) ) ),
    inference(subsumption_resolution,[],[f107,f49])).

fof(f107,plain,(
    ! [X9] :
      ( ~ r2_hidden(k1_funct_1(sK2,sK3(k1_relat_1(sK2),X9,sK2)),X9)
      | v1_funct_2(sK2,k1_relat_1(sK2),X9)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f51,f82])).

fof(f82,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k1_funct_1(X2,sK3(k1_relat_1(X2),X1,X2)),X1)
      | v1_funct_2(X2,k1_relat_1(X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(k1_funct_1(X2,sK3(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f198,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,sK3(k1_relat_1(sK2),X0,sK2)),sK0)
      | v1_funct_2(sK2,k1_relat_1(sK2),X0) ) ),
    inference(resolution,[],[f183,f50])).

fof(f183,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(sK2,X1)
      | r2_hidden(k1_funct_1(sK2,sK3(k1_relat_1(sK2),X0,sK2)),X1)
      | v1_funct_2(sK2,k1_relat_1(sK2),X0) ) ),
    inference(subsumption_resolution,[],[f182,f49])).

fof(f182,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(sK2,sK3(k1_relat_1(sK2),X0,sK2)),X1)
      | ~ v5_relat_1(sK2,X1)
      | v1_funct_2(sK2,k1_relat_1(sK2),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f180,f51])).

fof(f180,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(sK2,sK3(k1_relat_1(sK2),X0,sK2)),X1)
      | ~ v5_relat_1(sK2,X1)
      | v1_funct_2(sK2,k1_relat_1(sK2),X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f109,f83])).

fof(f83,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK3(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | v1_funct_2(X2,k1_relat_1(X2),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f224,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK0)
    | k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),sK0,sK2,sK0) ),
    inference(resolution,[],[f217,f105])).

fof(f105,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X7,X6)))
      | k1_xboole_0 = X6
      | ~ v1_funct_2(sK2,X7,X6)
      | k8_relset_1(X7,X6,sK2,X6) = X7 ) ),
    inference(resolution,[],[f51,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k8_relset_1(X0,X1,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

fof(f45,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:14:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (3424)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.44  % (3432)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.44  % (3424)Refutation not found, incomplete strategy% (3424)------------------------------
% 0.21/0.44  % (3424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (3432)Refutation not found, incomplete strategy% (3432)------------------------------
% 0.21/0.45  % (3432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (3424)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (3424)Memory used [KB]: 10618
% 0.21/0.45  % (3424)Time elapsed: 0.051 s
% 0.21/0.45  % (3424)------------------------------
% 0.21/0.45  % (3424)------------------------------
% 0.21/0.45  % (3432)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (3432)Memory used [KB]: 11001
% 0.21/0.45  % (3432)Time elapsed: 0.049 s
% 0.21/0.45  % (3432)------------------------------
% 0.21/0.45  % (3432)------------------------------
% 0.21/0.46  % (3436)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (3426)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (3436)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f281,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f239,f53])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.47  fof(f239,plain,(
% 0.21/0.47    ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    inference(backward_demodulation,[],[f45,f238])).
% 0.21/0.47  fof(f238,plain,(
% 0.21/0.47    k1_xboole_0 = sK0),
% 0.21/0.47    inference(subsumption_resolution,[],[f236,f156])).
% 0.21/0.47  fof(f156,plain,(
% 0.21/0.47    k1_relat_1(sK2) != k10_relat_1(sK2,sK0)),
% 0.21/0.47    inference(superposition,[],[f52,f136])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,sK0)),
% 0.21/0.47    inference(backward_demodulation,[],[f125,f131])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    sK0 = k1_relat_1(sK1)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f117,f113,f116,f65])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(nnf_transformation,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    v1_partfun1(sK1,sK0)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f45,f46,f47,f48,f61])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.47    inference(flattening,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ((k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v5_relat_1(sK2,sK0) & v1_relat_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)) & ~v1_xboole_0(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f40,f39,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & v1_funct_1(X2) & v5_relat_1(X2,sK0) & v1_relat_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X1,sK0,sK0) & v1_funct_1(X1)) & ~v1_xboole_0(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ? [X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & v1_funct_1(X2) & v5_relat_1(X2,sK0) & v1_relat_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X1,sK0,sK0) & v1_funct_1(X1)) => (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,sK1)) & v1_funct_1(X2) & v5_relat_1(X2,sK0) & v1_relat_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,sK1)) & v1_funct_1(X2) & v5_relat_1(X2,sK0) & v1_relat_1(X2)) => (k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v5_relat_1(sK2,sK0) & v1_relat_1(sK2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.47    inference(flattening,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & (v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))) & ~v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)))))),
% 0.21/0.47    inference(negated_conjecture,[],[f15])).
% 0.21/0.47  fof(f15,conjecture,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t200_funct_2)).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f41])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    v1_funct_1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f41])).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    v4_relat_1(sK1,sK0)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f48,f68])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    v1_relat_1(sK1)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f59,f48,f57])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,k1_relat_1(sK1))),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f49,f117,f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    v1_relat_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f41])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f41])).
% 0.21/0.47  fof(f236,plain,(
% 0.21/0.47    k1_relat_1(sK2) = k10_relat_1(sK2,sK0) | k1_xboole_0 = sK0),
% 0.21/0.47    inference(superposition,[],[f229,f219])).
% 0.21/0.47  fof(f219,plain,(
% 0.21/0.47    ( ! [X0] : (k8_relset_1(k1_relat_1(sK2),sK0,sK2,X0) = k10_relat_1(sK2,X0)) )),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f217,f78])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.47  fof(f217,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)))),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f214])).
% 0.21/0.47  fof(f214,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)))),
% 0.21/0.47    inference(resolution,[],[f213,f110])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    ( ! [X8] : (~r2_hidden(k1_funct_1(sK2,sK3(k1_relat_1(sK2),X8,sK2)),X8) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X8)))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f106,f49])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    ( ! [X8] : (~r2_hidden(k1_funct_1(sK2,sK3(k1_relat_1(sK2),X8,sK2)),X8) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X8))) | ~v1_relat_1(sK2)) )),
% 0.21/0.47    inference(resolution,[],[f51,f80])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    ( ! [X2,X1] : (~v1_funct_1(X2) | ~r2_hidden(k1_funct_1(X2,sK3(k1_relat_1(X2),X1,X2)),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(equality_resolution,[],[f75])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k1_funct_1(X2,sK3(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK3(X0,X1,X2)),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK3(X0,X1,X2)),X1) & r2_hidden(sK3(X0,X1,X2),X0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    v1_funct_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f41])).
% 0.21/0.47  fof(f213,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,sK3(k1_relat_1(sK2),X0,sK2)),sK0) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))) )),
% 0.21/0.47    inference(resolution,[],[f185,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    v5_relat_1(sK2,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f41])).
% 0.21/0.47  fof(f185,plain,(
% 0.21/0.47    ( ! [X2,X3] : (~v5_relat_1(sK2,X3) | r2_hidden(k1_funct_1(sK2,sK3(k1_relat_1(sK2),X2,sK2)),X3) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X2)))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f184,f49])).
% 0.21/0.47  fof(f184,plain,(
% 0.21/0.47    ( ! [X2,X3] : (r2_hidden(k1_funct_1(sK2,sK3(k1_relat_1(sK2),X2,sK2)),X3) | ~v5_relat_1(sK2,X3) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X2))) | ~v1_relat_1(sK2)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f181,f51])).
% 0.21/0.47  fof(f181,plain,(
% 0.21/0.47    ( ! [X2,X3] : (r2_hidden(k1_funct_1(sK2,sK3(k1_relat_1(sK2),X2,sK2)),X3) | ~v5_relat_1(sK2,X3) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X2))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.21/0.47    inference(resolution,[],[f109,f81])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    ( ! [X2,X1] : (r2_hidden(sK3(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(equality_resolution,[],[f74])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK3(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f44])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    ( ! [X4,X5] : (~r2_hidden(X4,k1_relat_1(sK2)) | r2_hidden(k1_funct_1(sK2,X4),X5) | ~v5_relat_1(sK2,X5)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f104,f49])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    ( ! [X4,X5] : (~r2_hidden(X4,k1_relat_1(sK2)) | r2_hidden(k1_funct_1(sK2,X4),X5) | ~v5_relat_1(sK2,X5) | ~v1_relat_1(sK2)) )),
% 0.21/0.47    inference(resolution,[],[f51,f67])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | r2_hidden(k1_funct_1(X1,X2),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).
% 0.21/0.47  fof(f229,plain,(
% 0.21/0.47    k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),sK0,sK2,sK0) | k1_xboole_0 = sK0),
% 0.21/0.47    inference(subsumption_resolution,[],[f224,f202])).
% 0.21/0.47  fof(f202,plain,(
% 0.21/0.47    v1_funct_2(sK2,k1_relat_1(sK2),sK0)),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f200])).
% 0.21/0.47  fof(f200,plain,(
% 0.21/0.47    v1_funct_2(sK2,k1_relat_1(sK2),sK0) | v1_funct_2(sK2,k1_relat_1(sK2),sK0)),
% 0.21/0.47    inference(resolution,[],[f198,f111])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    ( ! [X9] : (~r2_hidden(k1_funct_1(sK2,sK3(k1_relat_1(sK2),X9,sK2)),X9) | v1_funct_2(sK2,k1_relat_1(sK2),X9)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f107,f49])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    ( ! [X9] : (~r2_hidden(k1_funct_1(sK2,sK3(k1_relat_1(sK2),X9,sK2)),X9) | v1_funct_2(sK2,k1_relat_1(sK2),X9) | ~v1_relat_1(sK2)) )),
% 0.21/0.47    inference(resolution,[],[f51,f82])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    ( ! [X2,X1] : (~v1_funct_1(X2) | ~r2_hidden(k1_funct_1(X2,sK3(k1_relat_1(X2),X1,X2)),X1) | v1_funct_2(X2,k1_relat_1(X2),X1) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(equality_resolution,[],[f73])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(k1_funct_1(X2,sK3(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f44])).
% 0.21/0.47  fof(f198,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,sK3(k1_relat_1(sK2),X0,sK2)),sK0) | v1_funct_2(sK2,k1_relat_1(sK2),X0)) )),
% 0.21/0.47    inference(resolution,[],[f183,f50])).
% 0.21/0.47  fof(f183,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v5_relat_1(sK2,X1) | r2_hidden(k1_funct_1(sK2,sK3(k1_relat_1(sK2),X0,sK2)),X1) | v1_funct_2(sK2,k1_relat_1(sK2),X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f182,f49])).
% 0.21/0.47  fof(f182,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(k1_funct_1(sK2,sK3(k1_relat_1(sK2),X0,sK2)),X1) | ~v5_relat_1(sK2,X1) | v1_funct_2(sK2,k1_relat_1(sK2),X0) | ~v1_relat_1(sK2)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f180,f51])).
% 0.21/0.47  fof(f180,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(k1_funct_1(sK2,sK3(k1_relat_1(sK2),X0,sK2)),X1) | ~v5_relat_1(sK2,X1) | v1_funct_2(sK2,k1_relat_1(sK2),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.21/0.47    inference(resolution,[],[f109,f83])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    ( ! [X2,X1] : (r2_hidden(sK3(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | v1_funct_2(X2,k1_relat_1(X2),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(equality_resolution,[],[f72])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | r2_hidden(sK3(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f44])).
% 0.21/0.47  fof(f224,plain,(
% 0.21/0.47    k1_xboole_0 = sK0 | ~v1_funct_2(sK2,k1_relat_1(sK2),sK0) | k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),sK0,sK2,sK0)),
% 0.21/0.47    inference(resolution,[],[f217,f105])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    ( ! [X6,X7] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X7,X6))) | k1_xboole_0 = X6 | ~v1_funct_2(sK2,X7,X6) | k8_relset_1(X7,X6,sK2,X6) = X7) )),
% 0.21/0.47    inference(resolution,[],[f51,f76])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k8_relset_1(X0,X1,X2,X1) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.47    inference(flattening,[],[f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ~v1_xboole_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f41])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (3436)------------------------------
% 0.21/0.47  % (3436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (3436)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (3436)Memory used [KB]: 6396
% 0.21/0.47  % (3436)Time elapsed: 0.008 s
% 0.21/0.47  % (3436)------------------------------
% 0.21/0.47  % (3436)------------------------------
% 0.21/0.47  % (3420)Success in time 0.113 s
%------------------------------------------------------------------------------
