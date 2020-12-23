%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:30 EST 2020

% Result     : Theorem 1.03s
% Output     : Refutation 1.03s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 208 expanded)
%              Number of leaves         :   16 (  87 expanded)
%              Depth                    :   12
%              Number of atoms          :  243 (1313 expanded)
%              Number of equality atoms :   64 ( 246 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f148,plain,(
    $false ),
    inference(subsumption_resolution,[],[f143,f49])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f143,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(o_1_1_funct_2(k1_xboole_0))) ),
    inference(backward_demodulation,[],[f106,f128])).

fof(f128,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f127,f77])).

fof(f77,plain,(
    r2_hidden(sK3,sK0) ),
    inference(unit_resulting_resolution,[],[f42,f47,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f47,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3)
    & m1_subset_1(sK3,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f38,f37,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3)
                    & m1_subset_1(X3,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_partfun1(X1,X2,X3) != k3_funct_2(sK0,X1,X2,X3)
                  & m1_subset_1(X3,sK0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
              & v1_funct_2(X2,sK0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( k7_partfun1(X1,X2,X3) != k3_funct_2(sK0,X1,X2,X3)
                & m1_subset_1(X3,sK0) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
            & v1_funct_2(X2,sK0,X1)
            & v1_funct_1(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( k3_funct_2(sK0,sK1,X2,X3) != k7_partfun1(sK1,X2,X3)
              & m1_subset_1(X3,sK0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X2,sK0,sK1)
          & v1_funct_1(X2) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( k3_funct_2(sK0,sK1,X2,X3) != k7_partfun1(sK1,X2,X3)
            & m1_subset_1(X3,sK0) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X2,sK0,sK1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k3_funct_2(sK0,sK1,sK2,X3) != k7_partfun1(sK1,sK2,X3)
          & m1_subset_1(X3,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X3] :
        ( k3_funct_2(sK0,sK1,sK2,X3) != k7_partfun1(sK1,sK2,X3)
        & m1_subset_1(X3,sK0) )
   => ( k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3)
      & m1_subset_1(sK3,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3)
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3)
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,X0)
                   => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).

fof(f42,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f127,plain,
    ( ~ r2_hidden(sK3,sK0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f96,f121])).

fof(f121,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f95,f84])).

fof(f84,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f46,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f95,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f87,f45])).

fof(f45,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f87,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f46,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f96,plain,(
    ~ r2_hidden(sK3,k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f85,f44,f83,f94,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

fof(f94,plain,(
    k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3) ),
    inference(backward_demodulation,[],[f48,f82])).

fof(f82,plain,(
    k3_funct_2(sK0,sK1,sK2,sK3) = k1_funct_1(sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f42,f47,f44,f45,f46,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f48,plain,(
    k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f83,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f46,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f44,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f85,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f46,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f106,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(o_1_1_funct_2(sK1))) ),
    inference(unit_resulting_resolution,[],[f99,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f99,plain,(
    ~ r1_tarski(sK1,o_1_1_funct_2(sK1)) ),
    inference(unit_resulting_resolution,[],[f74,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f74,plain,(
    r2_hidden(o_1_1_funct_2(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f50,f43,f51])).

fof(f43,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f50,plain,(
    ! [X0] : m1_subset_1(o_1_1_funct_2(X0),X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(o_1_1_funct_2(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_1_1_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:55:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.38  ipcrm: permission denied for id (1234862081)
% 0.14/0.39  ipcrm: permission denied for id (1234894850)
% 0.14/0.39  ipcrm: permission denied for id (1241317379)
% 0.14/0.39  ipcrm: permission denied for id (1234960388)
% 0.14/0.39  ipcrm: permission denied for id (1234993157)
% 0.14/0.39  ipcrm: permission denied for id (1235025926)
% 0.14/0.39  ipcrm: permission denied for id (1235058695)
% 0.14/0.39  ipcrm: permission denied for id (1235124232)
% 0.14/0.39  ipcrm: permission denied for id (1238368265)
% 0.14/0.40  ipcrm: permission denied for id (1241350154)
% 0.14/0.40  ipcrm: permission denied for id (1238433803)
% 0.14/0.40  ipcrm: permission denied for id (1241382924)
% 0.14/0.40  ipcrm: permission denied for id (1241415693)
% 0.14/0.40  ipcrm: permission denied for id (1241448462)
% 0.14/0.40  ipcrm: permission denied for id (1238564879)
% 0.14/0.40  ipcrm: permission denied for id (1235353616)
% 0.14/0.41  ipcrm: permission denied for id (1238663186)
% 0.14/0.41  ipcrm: permission denied for id (1241514003)
% 0.14/0.41  ipcrm: permission denied for id (1238728724)
% 0.23/0.41  ipcrm: permission denied for id (1241546773)
% 0.23/0.41  ipcrm: permission denied for id (1238794262)
% 0.23/0.41  ipcrm: permission denied for id (1238827031)
% 0.23/0.41  ipcrm: permission denied for id (1241579544)
% 0.23/0.41  ipcrm: permission denied for id (1241612313)
% 0.23/0.42  ipcrm: permission denied for id (1241710620)
% 0.23/0.42  ipcrm: permission denied for id (1235550237)
% 0.23/0.42  ipcrm: permission denied for id (1235615775)
% 0.23/0.42  ipcrm: permission denied for id (1241808929)
% 0.23/0.42  ipcrm: permission denied for id (1235681314)
% 0.23/0.42  ipcrm: permission denied for id (1235714083)
% 0.23/0.42  ipcrm: permission denied for id (1239121956)
% 0.23/0.42  ipcrm: permission denied for id (1239154725)
% 0.23/0.42  ipcrm: permission denied for id (1239187494)
% 0.23/0.43  ipcrm: permission denied for id (1235845160)
% 0.23/0.43  ipcrm: permission denied for id (1235877929)
% 0.23/0.43  ipcrm: permission denied for id (1235910698)
% 0.23/0.43  ipcrm: permission denied for id (1241874475)
% 0.23/0.43  ipcrm: permission denied for id (1239285804)
% 0.23/0.43  ipcrm: permission denied for id (1236009005)
% 0.23/0.43  ipcrm: permission denied for id (1239318574)
% 0.23/0.43  ipcrm: permission denied for id (1239384111)
% 0.23/0.43  ipcrm: permission denied for id (1239416880)
% 0.23/0.43  ipcrm: permission denied for id (1239449649)
% 0.23/0.43  ipcrm: permission denied for id (1236140082)
% 0.23/0.44  ipcrm: permission denied for id (1236172851)
% 0.23/0.44  ipcrm: permission denied for id (1239482420)
% 0.23/0.44  ipcrm: permission denied for id (1241972790)
% 0.23/0.44  ipcrm: permission denied for id (1239580727)
% 0.23/0.44  ipcrm: permission denied for id (1239646264)
% 0.23/0.44  ipcrm: permission denied for id (1239679033)
% 0.23/0.44  ipcrm: permission denied for id (1239711802)
% 0.23/0.44  ipcrm: permission denied for id (1239744571)
% 0.23/0.44  ipcrm: permission denied for id (1236336700)
% 0.23/0.44  ipcrm: permission denied for id (1239777341)
% 0.23/0.44  ipcrm: permission denied for id (1242005566)
% 0.23/0.45  ipcrm: permission denied for id (1236435007)
% 0.23/0.45  ipcrm: permission denied for id (1242038336)
% 0.23/0.45  ipcrm: permission denied for id (1236500545)
% 0.23/0.45  ipcrm: permission denied for id (1236533314)
% 0.23/0.45  ipcrm: permission denied for id (1236566083)
% 0.23/0.45  ipcrm: permission denied for id (1236598852)
% 0.23/0.45  ipcrm: permission denied for id (1239875653)
% 0.23/0.45  ipcrm: permission denied for id (1239908422)
% 0.23/0.45  ipcrm: permission denied for id (1239941191)
% 0.23/0.45  ipcrm: permission denied for id (1236762696)
% 0.23/0.45  ipcrm: permission denied for id (1239973961)
% 0.23/0.46  ipcrm: permission denied for id (1240006730)
% 0.23/0.46  ipcrm: permission denied for id (1240072268)
% 0.23/0.46  ipcrm: permission denied for id (1240105037)
% 0.23/0.46  ipcrm: permission denied for id (1240137806)
% 0.23/0.46  ipcrm: permission denied for id (1240170575)
% 0.23/0.46  ipcrm: permission denied for id (1236992080)
% 0.23/0.46  ipcrm: permission denied for id (1240236113)
% 0.23/0.46  ipcrm: permission denied for id (1237057618)
% 0.23/0.47  ipcrm: permission denied for id (1240334421)
% 0.23/0.47  ipcrm: permission denied for id (1237221464)
% 0.23/0.47  ipcrm: permission denied for id (1237254233)
% 0.23/0.47  ipcrm: permission denied for id (1240432730)
% 0.23/0.47  ipcrm: permission denied for id (1240498268)
% 0.23/0.47  ipcrm: permission denied for id (1237418078)
% 0.23/0.47  ipcrm: permission denied for id (1237450847)
% 0.23/0.47  ipcrm: permission denied for id (1242300512)
% 0.23/0.48  ipcrm: permission denied for id (1240629346)
% 0.23/0.48  ipcrm: permission denied for id (1240662115)
% 0.23/0.48  ipcrm: permission denied for id (1237581924)
% 0.23/0.48  ipcrm: permission denied for id (1240694885)
% 0.23/0.48  ipcrm: permission denied for id (1237614695)
% 0.23/0.48  ipcrm: permission denied for id (1237647464)
% 0.23/0.49  ipcrm: permission denied for id (1240825963)
% 0.23/0.49  ipcrm: permission denied for id (1240858732)
% 0.23/0.49  ipcrm: permission denied for id (1240891501)
% 0.23/0.49  ipcrm: permission denied for id (1237844078)
% 0.23/0.49  ipcrm: permission denied for id (1240957040)
% 0.23/0.49  ipcrm: permission denied for id (1240989809)
% 0.23/0.49  ipcrm: permission denied for id (1241022578)
% 0.23/0.50  ipcrm: permission denied for id (1241055347)
% 0.23/0.50  ipcrm: permission denied for id (1237975156)
% 0.23/0.50  ipcrm: permission denied for id (1238007925)
% 0.23/0.50  ipcrm: permission denied for id (1238040695)
% 0.23/0.50  ipcrm: permission denied for id (1238073465)
% 0.23/0.50  ipcrm: permission denied for id (1241153658)
% 0.23/0.51  ipcrm: permission denied for id (1242562683)
% 0.23/0.51  ipcrm: permission denied for id (1238171772)
% 0.23/0.51  ipcrm: permission denied for id (1241219197)
% 0.23/0.51  ipcrm: permission denied for id (1241251966)
% 0.23/0.51  ipcrm: permission denied for id (1238270079)
% 1.03/0.63  % (18831)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.03/0.63  % (18831)Refutation not found, incomplete strategy% (18831)------------------------------
% 1.03/0.63  % (18831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.03/0.63  % (18831)Termination reason: Refutation not found, incomplete strategy
% 1.03/0.63  
% 1.03/0.63  % (18831)Memory used [KB]: 10618
% 1.03/0.63  % (18831)Time elapsed: 0.079 s
% 1.03/0.63  % (18831)------------------------------
% 1.03/0.63  % (18831)------------------------------
% 1.03/0.63  % (18843)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.03/0.63  % (18846)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.03/0.64  % (18849)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.03/0.64  % (18846)Refutation found. Thanks to Tanya!
% 1.03/0.64  % SZS status Theorem for theBenchmark
% 1.03/0.64  % SZS output start Proof for theBenchmark
% 1.03/0.64  fof(f148,plain,(
% 1.03/0.64    $false),
% 1.03/0.64    inference(subsumption_resolution,[],[f143,f49])).
% 1.03/0.64  fof(f49,plain,(
% 1.03/0.64    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.03/0.64    inference(cnf_transformation,[],[f2])).
% 1.03/0.64  fof(f2,axiom,(
% 1.03/0.64    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.03/0.64  fof(f143,plain,(
% 1.03/0.64    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(o_1_1_funct_2(k1_xboole_0)))),
% 1.03/0.64    inference(backward_demodulation,[],[f106,f128])).
% 1.03/0.64  fof(f128,plain,(
% 1.03/0.64    k1_xboole_0 = sK1),
% 1.03/0.64    inference(subsumption_resolution,[],[f127,f77])).
% 1.03/0.64  fof(f77,plain,(
% 1.03/0.64    r2_hidden(sK3,sK0)),
% 1.03/0.64    inference(unit_resulting_resolution,[],[f42,f47,f51])).
% 1.03/0.64  fof(f51,plain,(
% 1.03/0.64    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.03/0.64    inference(cnf_transformation,[],[f20])).
% 1.03/0.64  fof(f20,plain,(
% 1.03/0.64    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.03/0.64    inference(flattening,[],[f19])).
% 1.03/0.64  fof(f19,plain,(
% 1.03/0.64    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.03/0.64    inference(ennf_transformation,[],[f3])).
% 1.03/0.64  fof(f3,axiom,(
% 1.03/0.64    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.03/0.64  fof(f47,plain,(
% 1.03/0.64    m1_subset_1(sK3,sK0)),
% 1.03/0.64    inference(cnf_transformation,[],[f39])).
% 1.03/0.64  fof(f39,plain,(
% 1.03/0.64    (((k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3) & m1_subset_1(sK3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 1.03/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f38,f37,f36,f35])).
% 1.03/0.64  fof(f35,plain,(
% 1.03/0.64    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (k7_partfun1(X1,X2,X3) != k3_funct_2(sK0,X1,X2,X3) & m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X2,sK0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 1.03/0.64    introduced(choice_axiom,[])).
% 1.03/0.64  fof(f36,plain,(
% 1.03/0.64    ? [X1] : (? [X2] : (? [X3] : (k7_partfun1(X1,X2,X3) != k3_funct_2(sK0,X1,X2,X3) & m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X2,sK0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (k3_funct_2(sK0,sK1,X2,X3) != k7_partfun1(sK1,X2,X3) & m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X2,sK0,sK1) & v1_funct_1(X2)) & ~v1_xboole_0(sK1))),
% 1.03/0.64    introduced(choice_axiom,[])).
% 1.03/0.64  fof(f37,plain,(
% 1.03/0.64    ? [X2] : (? [X3] : (k3_funct_2(sK0,sK1,X2,X3) != k7_partfun1(sK1,X2,X3) & m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X2,sK0,sK1) & v1_funct_1(X2)) => (? [X3] : (k3_funct_2(sK0,sK1,sK2,X3) != k7_partfun1(sK1,sK2,X3) & m1_subset_1(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.03/0.64    introduced(choice_axiom,[])).
% 1.03/0.64  fof(f38,plain,(
% 1.03/0.64    ? [X3] : (k3_funct_2(sK0,sK1,sK2,X3) != k7_partfun1(sK1,sK2,X3) & m1_subset_1(X3,sK0)) => (k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3) & m1_subset_1(sK3,sK0))),
% 1.03/0.64    introduced(choice_axiom,[])).
% 1.03/0.64  fof(f18,plain,(
% 1.03/0.64    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.03/0.64    inference(flattening,[],[f17])).
% 1.03/0.64  fof(f17,plain,(
% 1.03/0.64    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3) & m1_subset_1(X3,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.03/0.64    inference(ennf_transformation,[],[f15])).
% 1.03/0.64  fof(f15,negated_conjecture,(
% 1.03/0.64    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 1.03/0.64    inference(negated_conjecture,[],[f14])).
% 1.03/0.64  fof(f14,conjecture,(
% 1.03/0.64    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 1.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).
% 1.03/0.64  fof(f42,plain,(
% 1.03/0.64    ~v1_xboole_0(sK0)),
% 1.03/0.64    inference(cnf_transformation,[],[f39])).
% 1.03/0.64  fof(f127,plain,(
% 1.03/0.64    ~r2_hidden(sK3,sK0) | k1_xboole_0 = sK1),
% 1.03/0.64    inference(superposition,[],[f96,f121])).
% 1.03/0.64  fof(f121,plain,(
% 1.03/0.64    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 1.03/0.64    inference(superposition,[],[f95,f84])).
% 1.03/0.64  fof(f84,plain,(
% 1.03/0.64    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.03/0.64    inference(unit_resulting_resolution,[],[f46,f57])).
% 1.03/0.64  fof(f57,plain,(
% 1.03/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.03/0.64    inference(cnf_transformation,[],[f25])).
% 1.03/0.64  fof(f25,plain,(
% 1.03/0.64    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.03/0.64    inference(ennf_transformation,[],[f9])).
% 1.03/0.64  fof(f9,axiom,(
% 1.03/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.03/0.64  fof(f46,plain,(
% 1.03/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.03/0.64    inference(cnf_transformation,[],[f39])).
% 1.03/0.64  fof(f95,plain,(
% 1.03/0.64    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 1.03/0.64    inference(subsumption_resolution,[],[f87,f45])).
% 1.03/0.64  fof(f45,plain,(
% 1.03/0.64    v1_funct_2(sK2,sK0,sK1)),
% 1.03/0.64    inference(cnf_transformation,[],[f39])).
% 1.03/0.64  fof(f87,plain,(
% 1.03/0.64    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.03/0.64    inference(resolution,[],[f46,f59])).
% 1.03/0.64  fof(f59,plain,(
% 1.03/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.03/0.64    inference(cnf_transformation,[],[f41])).
% 1.03/0.64  fof(f41,plain,(
% 1.03/0.64    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.03/0.64    inference(nnf_transformation,[],[f28])).
% 1.03/0.64  fof(f28,plain,(
% 1.03/0.64    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.03/0.64    inference(flattening,[],[f27])).
% 1.03/0.64  fof(f27,plain,(
% 1.03/0.64    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.03/0.64    inference(ennf_transformation,[],[f10])).
% 1.03/0.64  fof(f10,axiom,(
% 1.03/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.03/0.64  fof(f96,plain,(
% 1.03/0.64    ~r2_hidden(sK3,k1_relat_1(sK2))),
% 1.03/0.64    inference(unit_resulting_resolution,[],[f85,f44,f83,f94,f52])).
% 1.03/0.64  fof(f52,plain,(
% 1.03/0.64    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.03/0.64    inference(cnf_transformation,[],[f22])).
% 1.03/0.64  fof(f22,plain,(
% 1.03/0.64    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.03/0.64    inference(flattening,[],[f21])).
% 1.03/0.64  fof(f21,plain,(
% 1.03/0.64    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.03/0.64    inference(ennf_transformation,[],[f11])).
% 1.03/0.64  fof(f11,axiom,(
% 1.03/0.64    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 1.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).
% 1.03/0.64  fof(f94,plain,(
% 1.03/0.64    k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3)),
% 1.03/0.64    inference(backward_demodulation,[],[f48,f82])).
% 1.03/0.64  fof(f82,plain,(
% 1.03/0.64    k3_funct_2(sK0,sK1,sK2,sK3) = k1_funct_1(sK2,sK3)),
% 1.03/0.64    inference(unit_resulting_resolution,[],[f42,f47,f44,f45,f46,f67])).
% 1.03/0.64  fof(f67,plain,(
% 1.03/0.64    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | v1_xboole_0(X0)) )),
% 1.03/0.64    inference(cnf_transformation,[],[f34])).
% 1.03/0.64  fof(f34,plain,(
% 1.03/0.64    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.03/0.64    inference(flattening,[],[f33])).
% 1.03/0.64  fof(f33,plain,(
% 1.03/0.64    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.03/0.64    inference(ennf_transformation,[],[f13])).
% 1.03/0.64  fof(f13,axiom,(
% 1.03/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 1.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 1.03/0.64  fof(f48,plain,(
% 1.03/0.64    k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3)),
% 1.03/0.64    inference(cnf_transformation,[],[f39])).
% 1.03/0.64  fof(f83,plain,(
% 1.03/0.64    v5_relat_1(sK2,sK1)),
% 1.03/0.64    inference(unit_resulting_resolution,[],[f46,f58])).
% 1.03/0.64  fof(f58,plain,(
% 1.03/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.03/0.64    inference(cnf_transformation,[],[f26])).
% 1.03/0.64  fof(f26,plain,(
% 1.03/0.64    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.03/0.64    inference(ennf_transformation,[],[f16])).
% 1.03/0.64  fof(f16,plain,(
% 1.03/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.03/0.64    inference(pure_predicate_removal,[],[f8])).
% 1.03/0.64  fof(f8,axiom,(
% 1.03/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.03/0.64  fof(f44,plain,(
% 1.03/0.64    v1_funct_1(sK2)),
% 1.03/0.64    inference(cnf_transformation,[],[f39])).
% 1.03/0.64  fof(f85,plain,(
% 1.03/0.64    v1_relat_1(sK2)),
% 1.03/0.64    inference(unit_resulting_resolution,[],[f46,f56])).
% 1.03/0.64  fof(f56,plain,(
% 1.03/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.03/0.64    inference(cnf_transformation,[],[f24])).
% 1.03/0.64  fof(f24,plain,(
% 1.03/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.03/0.64    inference(ennf_transformation,[],[f7])).
% 1.03/0.64  fof(f7,axiom,(
% 1.03/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.03/0.64  fof(f106,plain,(
% 1.03/0.64    ~m1_subset_1(sK1,k1_zfmisc_1(o_1_1_funct_2(sK1)))),
% 1.03/0.64    inference(unit_resulting_resolution,[],[f99,f53])).
% 1.03/0.64  fof(f53,plain,(
% 1.03/0.64    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.03/0.64    inference(cnf_transformation,[],[f40])).
% 1.03/0.64  fof(f40,plain,(
% 1.03/0.64    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.03/0.64    inference(nnf_transformation,[],[f4])).
% 1.03/0.64  fof(f4,axiom,(
% 1.03/0.64    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.03/0.64  fof(f99,plain,(
% 1.03/0.64    ~r1_tarski(sK1,o_1_1_funct_2(sK1))),
% 1.03/0.64    inference(unit_resulting_resolution,[],[f74,f55])).
% 1.03/0.64  fof(f55,plain,(
% 1.03/0.64    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.03/0.64    inference(cnf_transformation,[],[f23])).
% 1.03/0.64  fof(f23,plain,(
% 1.03/0.64    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.03/0.64    inference(ennf_transformation,[],[f6])).
% 1.03/0.64  fof(f6,axiom,(
% 1.03/0.64    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.03/0.64  fof(f74,plain,(
% 1.03/0.64    r2_hidden(o_1_1_funct_2(sK1),sK1)),
% 1.03/0.64    inference(unit_resulting_resolution,[],[f50,f43,f51])).
% 1.03/0.64  fof(f43,plain,(
% 1.03/0.64    ~v1_xboole_0(sK1)),
% 1.03/0.64    inference(cnf_transformation,[],[f39])).
% 1.03/0.64  fof(f50,plain,(
% 1.03/0.64    ( ! [X0] : (m1_subset_1(o_1_1_funct_2(X0),X0)) )),
% 1.03/0.64    inference(cnf_transformation,[],[f12])).
% 1.03/0.64  fof(f12,axiom,(
% 1.03/0.64    ! [X0] : m1_subset_1(o_1_1_funct_2(X0),X0)),
% 1.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_1_1_funct_2)).
% 1.03/0.64  % SZS output end Proof for theBenchmark
% 1.03/0.64  % (18846)------------------------------
% 1.03/0.64  % (18846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.03/0.64  % (18846)Termination reason: Refutation
% 1.03/0.64  
% 1.03/0.64  % (18846)Memory used [KB]: 6268
% 1.03/0.64  % (18850)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.03/0.64  % (18846)Time elapsed: 0.026 s
% 1.03/0.64  % (18846)------------------------------
% 1.03/0.64  % (18846)------------------------------
% 1.03/0.64  % (18832)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 1.03/0.64  % (18834)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 1.03/0.64  % (18839)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.03/0.64  % (18833)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 1.03/0.64  % (18837)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.03/0.64  % (18847)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.03/0.64  % (18835)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.03/0.65  % (18672)Success in time 0.272 s
%------------------------------------------------------------------------------
