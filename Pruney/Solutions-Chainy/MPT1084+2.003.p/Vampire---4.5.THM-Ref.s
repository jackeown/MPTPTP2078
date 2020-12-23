%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:19 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 445 expanded)
%              Number of leaves         :   13 ( 131 expanded)
%              Depth                    :   23
%              Number of atoms          :  371 (2823 expanded)
%              Number of equality atoms :   93 ( 495 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f105,plain,(
    $false ),
    inference(subsumption_resolution,[],[f104,f89])).

fof(f89,plain,(
    r2_funct_2(sK0,sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f88,f40])).

fof(f40,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))
    & ! [X2] :
        ( k3_funct_2(sK0,sK0,sK1,X2) = X2
        | ~ m1_subset_1(X2,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
            & ! [X2] :
                ( k3_funct_2(X0,X0,X1,X2) = X2
                | ~ m1_subset_1(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ~ r2_funct_2(sK0,sK0,X1,k6_partfun1(sK0))
          & ! [X2] :
              ( k3_funct_2(sK0,sK0,X1,X2) = X2
              | ~ m1_subset_1(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_2(X1,sK0,sK0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ~ r2_funct_2(sK0,sK0,X1,k6_partfun1(sK0))
        & ! [X2] :
            ( k3_funct_2(sK0,sK0,X1,X2) = X2
            | ~ m1_subset_1(X2,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v1_funct_2(X1,sK0,sK0)
        & v1_funct_1(X1) )
   => ( ~ r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))
      & ! [X2] :
          ( k3_funct_2(sK0,sK0,sK1,X2) = X2
          | ~ m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
          & ! [X2] :
              ( k3_funct_2(X0,X0,X1,X2) = X2
              | ~ m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
          & ! [X2] :
              ( k3_funct_2(X0,X0,X1,X2) = X2
              | ~ m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X1,X0,X0)
              & v1_funct_1(X1) )
           => ( ! [X2] :
                  ( m1_subset_1(X2,X0)
                 => k3_funct_2(X0,X0,X1,X2) = X2 )
             => r2_funct_2(X0,X0,X1,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,X0)
               => k3_funct_2(X0,X0,X1,X2) = X2 )
           => r2_funct_2(X0,X0,X1,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t201_funct_2)).

fof(f88,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | r2_funct_2(sK0,sK0,sK1,sK1) ),
    inference(resolution,[],[f81,f41])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK1,X0,X1)
      | r2_funct_2(X0,X1,sK1,sK1) ) ),
    inference(resolution,[],[f67,f39])).

fof(f39,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_funct_2(X1,X2,X0,X0)
      | ~ v1_funct_2(X0,X1,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_funct_2(X1,X2,X0,X0)
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0) ) ),
    inference(condensation,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(f104,plain,(
    ~ r2_funct_2(sK0,sK0,sK1,sK1) ),
    inference(backward_demodulation,[],[f68,f103])).

fof(f103,plain,(
    sK1 = k6_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f102,f93])).

fof(f93,plain,
    ( sK2(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | sK1 = k6_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f92,f71])).

fof(f71,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f57,f41])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f92,plain,
    ( sK2(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | sK1 = k6_relat_1(sK0)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f91,f39])).

fof(f91,plain,
    ( sK2(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | sK1 = k6_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f61,f80])).

fof(f80,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f79,f71])).

fof(f79,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f78,f72])).

fof(f72,plain,(
    v4_relat_1(sK1,sK0) ),
    inference(resolution,[],[f58,f41])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f78,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ v4_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f77,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f77,plain,(
    v1_partfun1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f76,f38])).

fof(f38,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f76,plain,
    ( v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f75,f40])).

fof(f75,plain,
    ( v1_partfun1(sK1,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f74,f41])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(sK1,X0)
      | ~ v1_funct_2(sK1,X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f50,f39])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f61,plain,(
    ! [X1] :
      ( sK2(k1_relat_1(X1),X1) != k1_funct_1(X1,sK2(k1_relat_1(X1),X1))
      | k6_relat_1(k1_relat_1(X1)) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
            & r2_hidden(sK2(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f102,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | sK1 = k6_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | sK1 = k6_relat_1(sK0)
    | sK1 = k6_relat_1(sK0) ),
    inference(superposition,[],[f98,f87])).

fof(f87,plain,
    ( sK2(sK0,sK1) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1))
    | sK1 = k6_relat_1(sK0) ),
    inference(resolution,[],[f86,f42])).

fof(f42,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | k3_funct_2(sK0,sK0,sK1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f86,plain,
    ( m1_subset_1(sK2(sK0,sK1),sK0)
    | sK1 = k6_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f85,f38])).

fof(f85,plain,
    ( sK1 = k6_relat_1(sK0)
    | m1_subset_1(sK2(sK0,sK1),sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f84,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f84,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | sK1 = k6_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f83,f71])).

fof(f83,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | sK1 = k6_relat_1(sK0)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f82,f39])).

fof(f82,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | sK1 = k6_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f62,f80])).

fof(f62,plain,(
    ! [X1] :
      ( r2_hidden(sK2(k1_relat_1(X1),X1),k1_relat_1(X1))
      | k6_relat_1(k1_relat_1(X1)) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f98,plain,
    ( k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1)) = k1_funct_1(sK1,sK2(sK0,sK1))
    | sK1 = k6_relat_1(sK0) ),
    inference(resolution,[],[f97,f86])).

fof(f97,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f96,f38])).

fof(f96,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f95,f40])).

fof(f95,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | ~ v1_funct_2(sK1,sK0,sK0)
      | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f94,f41])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X0,X1)
      | ~ v1_funct_2(sK1,X1,X2)
      | k3_funct_2(X1,X2,sK1,X0) = k1_funct_1(sK1,X0)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f59,f39])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f68,plain,(
    ~ r2_funct_2(sK0,sK0,sK1,k6_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f43,f44])).

fof(f44,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f43,plain,(
    ~ r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:20:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.48  % (4596)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.48  % (4574)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.49  % (4582)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.49  % (4581)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.49  % (4574)Refutation found. Thanks to Tanya!
% 0.19/0.49  % SZS status Theorem for theBenchmark
% 0.19/0.49  % (4570)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.49  % SZS output start Proof for theBenchmark
% 0.19/0.49  fof(f105,plain,(
% 0.19/0.49    $false),
% 0.19/0.49    inference(subsumption_resolution,[],[f104,f89])).
% 0.19/0.49  fof(f89,plain,(
% 0.19/0.49    r2_funct_2(sK0,sK0,sK1,sK1)),
% 0.19/0.49    inference(subsumption_resolution,[],[f88,f40])).
% 0.19/0.49  fof(f40,plain,(
% 0.19/0.49    v1_funct_2(sK1,sK0,sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f30])).
% 0.19/0.49  fof(f30,plain,(
% 0.19/0.49    (~r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) & ! [X2] : (k3_funct_2(sK0,sK0,sK1,X2) = X2 | ~m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)) & ~v1_xboole_0(sK0)),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f29,f28])).
% 0.19/0.49  fof(f28,plain,(
% 0.19/0.49    ? [X0] : (? [X1] : (~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (~r2_funct_2(sK0,sK0,X1,k6_partfun1(sK0)) & ! [X2] : (k3_funct_2(sK0,sK0,X1,X2) = X2 | ~m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X1,sK0,sK0) & v1_funct_1(X1)) & ~v1_xboole_0(sK0))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f29,plain,(
% 0.19/0.49    ? [X1] : (~r2_funct_2(sK0,sK0,X1,k6_partfun1(sK0)) & ! [X2] : (k3_funct_2(sK0,sK0,X1,X2) = X2 | ~m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X1,sK0,sK0) & v1_funct_1(X1)) => (~r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) & ! [X2] : (k3_funct_2(sK0,sK0,sK1,X2) = X2 | ~m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f14,plain,(
% 0.19/0.49    ? [X0] : (? [X1] : (~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0))),
% 0.19/0.49    inference(flattening,[],[f13])).
% 0.19/0.49  fof(f13,plain,(
% 0.19/0.49    ? [X0] : (? [X1] : ((~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))) & ~v1_xboole_0(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f11])).
% 0.19/0.49  fof(f11,negated_conjecture,(
% 0.19/0.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (! [X2] : (m1_subset_1(X2,X0) => k3_funct_2(X0,X0,X1,X2) = X2) => r2_funct_2(X0,X0,X1,k6_partfun1(X0)))))),
% 0.19/0.49    inference(negated_conjecture,[],[f10])).
% 0.19/0.49  fof(f10,conjecture,(
% 0.19/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (! [X2] : (m1_subset_1(X2,X0) => k3_funct_2(X0,X0,X1,X2) = X2) => r2_funct_2(X0,X0,X1,k6_partfun1(X0)))))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t201_funct_2)).
% 0.19/0.49  fof(f88,plain,(
% 0.19/0.49    ~v1_funct_2(sK1,sK0,sK0) | r2_funct_2(sK0,sK0,sK1,sK1)),
% 0.19/0.49    inference(resolution,[],[f81,f41])).
% 0.19/0.49  fof(f41,plain,(
% 0.19/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.49    inference(cnf_transformation,[],[f30])).
% 0.19/0.49  fof(f81,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK1,X0,X1) | r2_funct_2(X0,X1,sK1,sK1)) )),
% 0.19/0.49    inference(resolution,[],[f67,f39])).
% 0.19/0.49  fof(f39,plain,(
% 0.19/0.49    v1_funct_1(sK1)),
% 0.19/0.49    inference(cnf_transformation,[],[f30])).
% 0.19/0.49  fof(f67,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | r2_funct_2(X1,X2,X0,X0) | ~v1_funct_2(X0,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.19/0.49    inference(duplicate_literal_removal,[],[f66])).
% 0.19/0.49  fof(f66,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_funct_2(X1,X2,X0,X0) | ~v1_funct_2(X0,X1,X2) | ~v1_funct_1(X0) | ~v1_funct_2(X0,X1,X2) | ~v1_funct_1(X0)) )),
% 0.19/0.49    inference(condensation,[],[f60])).
% 0.19/0.49  fof(f60,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f27])).
% 0.19/0.49  fof(f27,plain,(
% 0.19/0.49    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.19/0.49    inference(flattening,[],[f26])).
% 0.19/0.49  fof(f26,plain,(
% 0.19/0.49    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.19/0.49    inference(ennf_transformation,[],[f9])).
% 0.19/0.49  fof(f9,axiom,(
% 0.19/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).
% 0.19/0.49  fof(f104,plain,(
% 0.19/0.49    ~r2_funct_2(sK0,sK0,sK1,sK1)),
% 0.19/0.49    inference(backward_demodulation,[],[f68,f103])).
% 0.19/0.49  fof(f103,plain,(
% 0.19/0.49    sK1 = k6_relat_1(sK0)),
% 0.19/0.49    inference(subsumption_resolution,[],[f102,f93])).
% 0.19/0.49  fof(f93,plain,(
% 0.19/0.49    sK2(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1)) | sK1 = k6_relat_1(sK0)),
% 0.19/0.49    inference(subsumption_resolution,[],[f92,f71])).
% 0.19/0.49  fof(f71,plain,(
% 0.19/0.49    v1_relat_1(sK1)),
% 0.19/0.49    inference(resolution,[],[f57,f41])).
% 0.19/0.49  fof(f57,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f22])).
% 0.19/0.49  fof(f22,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.49    inference(ennf_transformation,[],[f3])).
% 0.19/0.49  fof(f3,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.19/0.49  fof(f92,plain,(
% 0.19/0.49    sK2(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1)) | sK1 = k6_relat_1(sK0) | ~v1_relat_1(sK1)),
% 0.19/0.49    inference(subsumption_resolution,[],[f91,f39])).
% 0.19/0.49  fof(f91,plain,(
% 0.19/0.49    sK2(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1)) | sK1 = k6_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.19/0.49    inference(superposition,[],[f61,f80])).
% 0.19/0.49  fof(f80,plain,(
% 0.19/0.49    sK0 = k1_relat_1(sK1)),
% 0.19/0.49    inference(subsumption_resolution,[],[f79,f71])).
% 0.19/0.49  fof(f79,plain,(
% 0.19/0.49    sK0 = k1_relat_1(sK1) | ~v1_relat_1(sK1)),
% 0.19/0.49    inference(subsumption_resolution,[],[f78,f72])).
% 0.19/0.49  fof(f72,plain,(
% 0.19/0.49    v4_relat_1(sK1,sK0)),
% 0.19/0.49    inference(resolution,[],[f58,f41])).
% 0.19/0.49  fof(f58,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f23])).
% 0.19/0.49  fof(f23,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.49    inference(ennf_transformation,[],[f12])).
% 0.19/0.49  fof(f12,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.19/0.49    inference(pure_predicate_removal,[],[f4])).
% 0.19/0.49  fof(f4,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.49  fof(f78,plain,(
% 0.19/0.49    sK0 = k1_relat_1(sK1) | ~v4_relat_1(sK1,sK0) | ~v1_relat_1(sK1)),
% 0.19/0.49    inference(resolution,[],[f77,f55])).
% 0.19/0.49  fof(f55,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f37])).
% 0.19/0.49  fof(f37,plain,(
% 0.19/0.49    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.49    inference(nnf_transformation,[],[f21])).
% 0.19/0.49  fof(f21,plain,(
% 0.19/0.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.49    inference(flattening,[],[f20])).
% 0.19/0.49  fof(f20,plain,(
% 0.19/0.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.19/0.49    inference(ennf_transformation,[],[f6])).
% 0.19/0.49  fof(f6,axiom,(
% 0.19/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.19/0.49  fof(f77,plain,(
% 0.19/0.49    v1_partfun1(sK1,sK0)),
% 0.19/0.49    inference(subsumption_resolution,[],[f76,f38])).
% 0.19/0.49  fof(f38,plain,(
% 0.19/0.49    ~v1_xboole_0(sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f30])).
% 0.19/0.49  fof(f76,plain,(
% 0.19/0.49    v1_partfun1(sK1,sK0) | v1_xboole_0(sK0)),
% 0.19/0.49    inference(subsumption_resolution,[],[f75,f40])).
% 0.19/0.49  fof(f75,plain,(
% 0.19/0.49    v1_partfun1(sK1,sK0) | ~v1_funct_2(sK1,sK0,sK0) | v1_xboole_0(sK0)),
% 0.19/0.49    inference(resolution,[],[f74,f41])).
% 0.19/0.49  fof(f74,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(sK1,X0) | ~v1_funct_2(sK1,X0,X1) | v1_xboole_0(X1)) )),
% 0.19/0.49    inference(resolution,[],[f50,f39])).
% 0.19/0.49  fof(f50,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f17])).
% 0.19/0.49  fof(f17,plain,(
% 0.19/0.49    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.19/0.49    inference(flattening,[],[f16])).
% 0.19/0.49  fof(f16,plain,(
% 0.19/0.49    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.19/0.49    inference(ennf_transformation,[],[f5])).
% 0.19/0.49  fof(f5,axiom,(
% 0.19/0.49    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.19/0.49  fof(f61,plain,(
% 0.19/0.49    ( ! [X1] : (sK2(k1_relat_1(X1),X1) != k1_funct_1(X1,sK2(k1_relat_1(X1),X1)) | k6_relat_1(k1_relat_1(X1)) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.49    inference(equality_resolution,[],[f54])).
% 0.19/0.49  fof(f54,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f36])).
% 0.19/0.49  fof(f36,plain,(
% 0.19/0.49    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).
% 0.19/0.49  fof(f35,plain,(
% 0.19/0.49    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f34,plain,(
% 0.19/0.49    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.49    inference(rectify,[],[f33])).
% 0.19/0.49  fof(f33,plain,(
% 0.19/0.49    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.49    inference(flattening,[],[f32])).
% 0.19/0.49  fof(f32,plain,(
% 0.19/0.49    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.49    inference(nnf_transformation,[],[f19])).
% 0.19/0.49  fof(f19,plain,(
% 0.19/0.49    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.49    inference(flattening,[],[f18])).
% 0.19/0.49  fof(f18,plain,(
% 0.19/0.49    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.19/0.49    inference(ennf_transformation,[],[f2])).
% 0.19/0.49  fof(f2,axiom,(
% 0.19/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 0.19/0.49  fof(f102,plain,(
% 0.19/0.49    sK2(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | sK1 = k6_relat_1(sK0)),
% 0.19/0.49    inference(duplicate_literal_removal,[],[f99])).
% 0.19/0.49  fof(f99,plain,(
% 0.19/0.49    sK2(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | sK1 = k6_relat_1(sK0) | sK1 = k6_relat_1(sK0)),
% 0.19/0.49    inference(superposition,[],[f98,f87])).
% 0.19/0.49  fof(f87,plain,(
% 0.19/0.49    sK2(sK0,sK1) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1)) | sK1 = k6_relat_1(sK0)),
% 0.19/0.49    inference(resolution,[],[f86,f42])).
% 0.19/0.49  fof(f42,plain,(
% 0.19/0.49    ( ! [X2] : (~m1_subset_1(X2,sK0) | k3_funct_2(sK0,sK0,sK1,X2) = X2) )),
% 0.19/0.49    inference(cnf_transformation,[],[f30])).
% 0.19/0.49  fof(f86,plain,(
% 0.19/0.49    m1_subset_1(sK2(sK0,sK1),sK0) | sK1 = k6_relat_1(sK0)),
% 0.19/0.49    inference(subsumption_resolution,[],[f85,f38])).
% 0.19/0.49  fof(f85,plain,(
% 0.19/0.49    sK1 = k6_relat_1(sK0) | m1_subset_1(sK2(sK0,sK1),sK0) | v1_xboole_0(sK0)),
% 0.19/0.49    inference(resolution,[],[f84,f46])).
% 0.19/0.49  fof(f46,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f31])).
% 0.19/0.49  fof(f31,plain,(
% 0.19/0.49    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.19/0.49    inference(nnf_transformation,[],[f15])).
% 0.19/0.49  fof(f15,plain,(
% 0.19/0.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f1])).
% 0.19/0.49  fof(f1,axiom,(
% 0.19/0.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.19/0.49  fof(f84,plain,(
% 0.19/0.49    r2_hidden(sK2(sK0,sK1),sK0) | sK1 = k6_relat_1(sK0)),
% 0.19/0.49    inference(subsumption_resolution,[],[f83,f71])).
% 0.19/0.49  fof(f83,plain,(
% 0.19/0.49    r2_hidden(sK2(sK0,sK1),sK0) | sK1 = k6_relat_1(sK0) | ~v1_relat_1(sK1)),
% 0.19/0.49    inference(subsumption_resolution,[],[f82,f39])).
% 0.19/0.49  fof(f82,plain,(
% 0.19/0.49    r2_hidden(sK2(sK0,sK1),sK0) | sK1 = k6_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.19/0.49    inference(superposition,[],[f62,f80])).
% 0.19/0.49  fof(f62,plain,(
% 0.19/0.49    ( ! [X1] : (r2_hidden(sK2(k1_relat_1(X1),X1),k1_relat_1(X1)) | k6_relat_1(k1_relat_1(X1)) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.49    inference(equality_resolution,[],[f53])).
% 0.19/0.49  fof(f53,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f36])).
% 0.19/0.49  fof(f98,plain,(
% 0.19/0.49    k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1)) = k1_funct_1(sK1,sK2(sK0,sK1)) | sK1 = k6_relat_1(sK0)),
% 0.19/0.49    inference(resolution,[],[f97,f86])).
% 0.19/0.49  fof(f97,plain,(
% 0.19/0.49    ( ! [X0] : (~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0)) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f96,f38])).
% 0.19/0.49  fof(f96,plain,(
% 0.19/0.49    ( ! [X0] : (~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0) | v1_xboole_0(sK0)) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f95,f40])).
% 0.19/0.49  fof(f95,plain,(
% 0.19/0.49    ( ! [X0] : (~m1_subset_1(X0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0) | v1_xboole_0(sK0)) )),
% 0.19/0.49    inference(resolution,[],[f94,f41])).
% 0.19/0.49  fof(f94,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,X1) | ~v1_funct_2(sK1,X1,X2) | k3_funct_2(X1,X2,sK1,X0) = k1_funct_1(sK1,X0) | v1_xboole_0(X1)) )),
% 0.19/0.49    inference(resolution,[],[f59,f39])).
% 0.19/0.49  fof(f59,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | v1_xboole_0(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f25])).
% 0.19/0.49  fof(f25,plain,(
% 0.19/0.49    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.19/0.49    inference(flattening,[],[f24])).
% 0.19/0.49  fof(f24,plain,(
% 0.19/0.49    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f7])).
% 0.19/0.49  fof(f7,axiom,(
% 0.19/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.19/0.49  fof(f68,plain,(
% 0.19/0.49    ~r2_funct_2(sK0,sK0,sK1,k6_relat_1(sK0))),
% 0.19/0.49    inference(backward_demodulation,[],[f43,f44])).
% 0.19/0.49  fof(f44,plain,(
% 0.19/0.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f8])).
% 0.19/0.49  fof(f8,axiom,(
% 0.19/0.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.19/0.49  fof(f43,plain,(
% 0.19/0.49    ~r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))),
% 0.19/0.49    inference(cnf_transformation,[],[f30])).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (4574)------------------------------
% 0.19/0.49  % (4574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (4574)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (4574)Memory used [KB]: 6268
% 0.19/0.49  % (4574)Time elapsed: 0.091 s
% 0.19/0.49  % (4574)------------------------------
% 0.19/0.49  % (4574)------------------------------
% 0.19/0.49  % (4589)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.50  % (4566)Success in time 0.145 s
%------------------------------------------------------------------------------
