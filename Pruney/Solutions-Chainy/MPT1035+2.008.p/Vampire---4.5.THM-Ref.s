%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  144 (59692 expanded)
%              Number of leaves         :    9 (12017 expanded)
%              Depth                    :   56
%              Number of atoms          :  496 (342057 expanded)
%              Number of equality atoms :  173 (100119 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f511,plain,(
    $false ),
    inference(resolution,[],[f504,f268])).

fof(f268,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f261,f265])).

fof(f265,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f264])).

fof(f264,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f26,f258])).

fof(f258,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f251,f31])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( r1_partfun1(X2,X3)
          <~> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( r1_partfun1(X2,X3)
          <~> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ( k1_xboole_0 = X1
               => k1_xboole_0 = X0 )
             => ( r1_partfun1(X2,X3)
              <=> ! [X4] :
                    ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                   => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ( k1_xboole_0 = X1
             => k1_xboole_0 = X0 )
           => ( r1_partfun1(X2,X3)
            <=> ! [X4] :
                  ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_2)).

fof(f251,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f250,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f250,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f249,f94])).

fof(f94,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f91,f36])).

fof(f36,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f91,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f31,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f249,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f247,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f247,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f246])).

fof(f246,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f242,f122])).

fof(f122,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f69,f74])).

fof(f74,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f29,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f69,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f68,f29])).

fof(f68,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f28,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f28,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f242,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f241,f219])).

fof(f219,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f218,f31])).

fof(f218,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | k1_xboole_0 = sK1
      | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) ) ),
    inference(subsumption_resolution,[],[f216,f207])).

fof(f207,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f206,f24])).

fof(f24,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f12])).

fof(f206,plain,
    ( r1_partfun1(sK2,sK3)
    | k1_xboole_0 = sK1
    | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) ),
    inference(resolution,[],[f196,f31])).

fof(f196,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))
      | k1_xboole_0 = sK1
      | r1_partfun1(sK2,sK3) ) ),
    inference(resolution,[],[f195,f41])).

fof(f195,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f192,f122])).

fof(f192,plain,
    ( ~ v4_relat_1(sK2,k1_relat_1(sK3))
    | r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f190,f94])).

fof(f190,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3)
    | ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,k1_relat_1(sK3)) ),
    inference(resolution,[],[f188,f38])).

fof(f188,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f187,f76])).

fof(f76,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f75,f36])).

fof(f75,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f29,f32])).

fof(f187,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) ),
    inference(duplicate_literal_removal,[],[f185])).

fof(f185,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | r1_partfun1(sK2,sK3) ),
    inference(resolution,[],[f148,f27])).

fof(f27,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f148,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | r1_partfun1(sK2,sK3)
      | ~ v1_relat_1(X0)
      | k1_funct_1(sK2,sK5(sK2,X0)) = k1_funct_1(sK3,sK5(sK2,X0))
      | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X0))
      | r1_partfun1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f147,f30])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f147,plain,(
    ! [X0] :
      ( k1_funct_1(sK2,sK5(sK2,X0)) = k1_funct_1(sK3,sK5(sK2,X0))
      | r1_partfun1(sK2,sK3)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X0))
      | r1_partfun1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f146,f94])).

fof(f146,plain,(
    ! [X0] :
      ( k1_funct_1(sK2,sK5(sK2,X0)) = k1_funct_1(sK3,sK5(sK2,X0))
      | r1_partfun1(sK2,sK3)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X0))
      | r1_partfun1(sK2,X0) ) ),
    inference(resolution,[],[f93,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | r1_partfun1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
           => ( r1_partfun1(X0,X1)
            <=> ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_partfun1)).

fof(f93,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_relat_1(sK2))
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
      | r1_partfun1(sK2,sK3) ) ),
    inference(backward_demodulation,[],[f25,f90])).

fof(f90,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f31,f40])).

fof(f25,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_relset_1(sK0,sK1,sK2))
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
      | r1_partfun1(sK2,sK3) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f216,plain,(
    ! [X0] :
      ( k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
      | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
      | k1_xboole_0 = sK1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ) ),
    inference(resolution,[],[f184,f41])).

fof(f184,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f181,f122])).

fof(f181,plain,
    ( ~ v4_relat_1(sK2,k1_relat_1(sK3))
    | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f179,f94])).

fof(f179,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,k1_relat_1(sK3)) ),
    inference(resolution,[],[f115,f38])).

fof(f115,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f114,f27])).

fof(f114,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | ~ v1_funct_1(sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f113,f76])).

fof(f113,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f112,f30])).

fof(f112,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f111,f94])).

fof(f111,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) ),
    inference(resolution,[],[f24,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
      | r1_partfun1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f241,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f240,f27])).

fof(f240,plain,
    ( ~ v1_funct_1(sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f239,f76])).

fof(f239,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f233])).

fof(f233,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f229,f227])).

fof(f227,plain,
    ( r1_partfun1(sK2,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f225,f219])).

fof(f225,plain,
    ( k1_xboole_0 = sK1
    | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
    | r1_partfun1(sK2,sK3) ),
    inference(resolution,[],[f224,f93])).

fof(f224,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f223,f208])).

fof(f208,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f206,f92])).

fof(f92,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | r2_hidden(sK4,k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f23,f90])).

fof(f23,plain,
    ( r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2))
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f223,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | k1_xboole_0 = sK1
    | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) ),
    inference(resolution,[],[f175,f31])).

fof(f175,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | r2_hidden(sK4,k1_relat_1(sK2))
      | k1_xboole_0 = sK1
      | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) ) ),
    inference(resolution,[],[f174,f41])).

fof(f174,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | r2_hidden(sK4,k1_relat_1(sK2))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f171,f122])).

fof(f171,plain,
    ( ~ v4_relat_1(sK2,k1_relat_1(sK3))
    | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | r2_hidden(sK4,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f169,f94])).

fof(f169,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,k1_relat_1(sK3)) ),
    inference(resolution,[],[f109,f38])).

fof(f109,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | r2_hidden(sK4,k1_relat_1(sK2))
    | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f108,f27])).

fof(f108,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | ~ v1_funct_1(sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f107,f76])).

fof(f107,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f106,f30])).

fof(f106,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f105,f94])).

fof(f105,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) ),
    inference(resolution,[],[f92,f35])).

fof(f229,plain,(
    ! [X0] :
      ( ~ r1_partfun1(sK2,X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X0))
      | k1_funct_1(sK2,sK4) = k1_funct_1(X0,sK4)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f228,f30])).

fof(f228,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X0))
      | k1_funct_1(sK2,sK4) = k1_funct_1(X0,sK4)
      | ~ r1_partfun1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f226,f94])).

fof(f226,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X0))
      | k1_funct_1(sK2,sK4) = k1_funct_1(X0,sK4)
      | ~ r1_partfun1(sK2,X0) ) ),
    inference(resolution,[],[f224,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
      | ~ r1_partfun1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f26,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f12])).

fof(f261,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f31,f258])).

fof(f504,plain,(
    ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ),
    inference(resolution,[],[f503,f41])).

fof(f503,plain,(
    ~ v4_relat_1(sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f497,f94])).

fof(f497,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,k1_xboole_0) ),
    inference(resolution,[],[f490,f38])).

fof(f490,plain,(
    ~ r1_tarski(k1_relat_1(sK2),k1_xboole_0) ),
    inference(forward_demodulation,[],[f489,f282])).

fof(f282,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f269,f281])).

fof(f281,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(subsumption_resolution,[],[f271,f267])).

fof(f267,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f260,f265])).

fof(f260,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f29,f258])).

fof(f271,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(resolution,[],[f266,f60])).

fof(f60,plain,(
    ! [X8] :
      ( ~ v1_funct_2(sK3,X8,X8)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X8)))
      | k1_relset_1(X8,X8,sK3) = X8 ) ),
    inference(resolution,[],[f27,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f266,plain,(
    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f259,f265])).

fof(f259,plain,(
    v1_funct_2(sK3,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f28,f258])).

fof(f269,plain,(
    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f262,f265])).

fof(f262,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f74,f258])).

fof(f489,plain,(
    ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f488,f76])).

fof(f488,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f487,f475])).

fof(f475,plain,(
    k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f469,f436])).

fof(f436,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) ),
    inference(resolution,[],[f424,f24])).

fof(f424,plain,
    ( r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) ),
    inference(resolution,[],[f291,f268])).

fof(f291,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))
      | r1_partfun1(sK2,sK3) ) ),
    inference(backward_demodulation,[],[f193,f282])).

fof(f193,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
      | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))
      | r1_partfun1(sK2,sK3) ) ),
    inference(resolution,[],[f192,f41])).

fof(f469,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) ),
    inference(resolution,[],[f288,f268])).

fof(f288,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
      | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) ) ),
    inference(backward_demodulation,[],[f182,f282])).

fof(f182,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
      | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
      | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) ) ),
    inference(resolution,[],[f181,f41])).

fof(f487,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f486,f27])).

fof(f486,plain,
    ( ~ v1_funct_1(sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
    | ~ v1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f481])).

fof(f481,plain,
    ( ~ v1_funct_1(sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) ),
    inference(resolution,[],[f468,f465])).

fof(f465,plain,
    ( r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) ),
    inference(resolution,[],[f464,f93])).

fof(f464,plain,(
    r2_hidden(sK4,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f458,f437])).

fof(f437,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) ),
    inference(resolution,[],[f424,f92])).

fof(f458,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) ),
    inference(resolution,[],[f286,f268])).

fof(f286,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | r2_hidden(sK4,k1_relat_1(sK2))
      | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) ) ),
    inference(backward_demodulation,[],[f172,f282])).

fof(f172,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
      | r2_hidden(sK4,k1_relat_1(sK2))
      | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) ) ),
    inference(resolution,[],[f171,f41])).

fof(f468,plain,(
    ! [X0] :
      ( ~ r1_partfun1(sK2,X0)
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X0))
      | k1_funct_1(sK2,sK4) = k1_funct_1(X0,sK4)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f467,f30])).

fof(f467,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X0))
      | k1_funct_1(sK2,sK4) = k1_funct_1(X0,sK4)
      | ~ r1_partfun1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f466,f94])).

fof(f466,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X0))
      | k1_funct_1(sK2,sK4) = k1_funct_1(X0,sK4)
      | ~ r1_partfun1(sK2,X0) ) ),
    inference(resolution,[],[f464,f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:49:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (617)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.42  % (617)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f511,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(resolution,[],[f504,f268])).
% 0.21/0.42  fof(f268,plain,(
% 0.21/0.42    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.42    inference(backward_demodulation,[],[f261,f265])).
% 0.21/0.42  fof(f265,plain,(
% 0.21/0.42    k1_xboole_0 = sK0),
% 0.21/0.42    inference(trivial_inequality_removal,[],[f264])).
% 0.21/0.42  fof(f264,plain,(
% 0.21/0.42    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0),
% 0.21/0.42    inference(superposition,[],[f26,f258])).
% 0.21/0.42  fof(f258,plain,(
% 0.21/0.42    k1_xboole_0 = sK1),
% 0.21/0.42    inference(resolution,[],[f251,f31])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (? [X3] : ((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.21/0.42    inference(flattening,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (? [X3] : (((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.21/0.42    inference(ennf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 0.21/0.42    inference(negated_conjecture,[],[f9])).
% 0.21/0.42  fof(f9,conjecture,(
% 0.21/0.42    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_2)).
% 0.21/0.42  fof(f251,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | k1_xboole_0 = sK1) )),
% 0.21/0.42    inference(resolution,[],[f250,f41])).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.42  fof(f250,plain,(
% 0.21/0.42    ~v4_relat_1(sK2,sK0) | k1_xboole_0 = sK1),
% 0.21/0.42    inference(subsumption_resolution,[],[f249,f94])).
% 0.21/0.42  fof(f94,plain,(
% 0.21/0.42    v1_relat_1(sK2)),
% 0.21/0.42    inference(subsumption_resolution,[],[f91,f36])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.42  fof(f91,plain,(
% 0.21/0.42    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 0.21/0.42    inference(resolution,[],[f31,f32])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.42  fof(f249,plain,(
% 0.21/0.42    k1_xboole_0 = sK1 | ~v1_relat_1(sK2) | ~v4_relat_1(sK2,sK0)),
% 0.21/0.42    inference(resolution,[],[f247,f38])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.42  fof(f247,plain,(
% 0.21/0.42    ~r1_tarski(k1_relat_1(sK2),sK0) | k1_xboole_0 = sK1),
% 0.21/0.42    inference(duplicate_literal_removal,[],[f246])).
% 0.21/0.42  fof(f246,plain,(
% 0.21/0.42    ~r1_tarski(k1_relat_1(sK2),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.21/0.42    inference(superposition,[],[f242,f122])).
% 0.21/0.42  fof(f122,plain,(
% 0.21/0.42    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 0.21/0.42    inference(superposition,[],[f69,f74])).
% 0.21/0.42  fof(f74,plain,(
% 0.21/0.42    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.42    inference(resolution,[],[f29,f40])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f69,plain,(
% 0.21/0.42    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 0.21/0.42    inference(subsumption_resolution,[],[f68,f29])).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.42    inference(resolution,[],[f28,f48])).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    inference(flattening,[],[f21])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f242,plain,(
% 0.21/0.42    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | k1_xboole_0 = sK1),
% 0.21/0.42    inference(subsumption_resolution,[],[f241,f219])).
% 0.21/0.42  fof(f219,plain,(
% 0.21/0.42    k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) | k1_xboole_0 = sK1),
% 0.21/0.42    inference(resolution,[],[f218,f31])).
% 0.21/0.42  fof(f218,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | k1_xboole_0 = sK1 | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)) )),
% 0.21/0.42    inference(subsumption_resolution,[],[f216,f207])).
% 0.21/0.42  fof(f207,plain,(
% 0.21/0.42    k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) | k1_xboole_0 = sK1),
% 0.21/0.42    inference(resolution,[],[f206,f24])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ~r1_partfun1(sK2,sK3) | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f206,plain,(
% 0.21/0.42    r1_partfun1(sK2,sK3) | k1_xboole_0 = sK1 | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))),
% 0.21/0.42    inference(resolution,[],[f196,f31])).
% 0.21/0.42  fof(f196,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) | k1_xboole_0 = sK1 | r1_partfun1(sK2,sK3)) )),
% 0.21/0.42    inference(resolution,[],[f195,f41])).
% 0.21/0.42  fof(f195,plain,(
% 0.21/0.42    ~v4_relat_1(sK2,sK0) | r1_partfun1(sK2,sK3) | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) | k1_xboole_0 = sK1),
% 0.21/0.42    inference(superposition,[],[f192,f122])).
% 0.21/0.42  fof(f192,plain,(
% 0.21/0.42    ~v4_relat_1(sK2,k1_relat_1(sK3)) | r1_partfun1(sK2,sK3) | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))),
% 0.21/0.42    inference(subsumption_resolution,[],[f190,f94])).
% 0.21/0.42  fof(f190,plain,(
% 0.21/0.42    k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) | r1_partfun1(sK2,sK3) | ~v1_relat_1(sK2) | ~v4_relat_1(sK2,k1_relat_1(sK3))),
% 0.21/0.42    inference(resolution,[],[f188,f38])).
% 0.21/0.42  fof(f188,plain,(
% 0.21/0.42    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) | r1_partfun1(sK2,sK3)),
% 0.21/0.42    inference(subsumption_resolution,[],[f187,f76])).
% 0.21/0.42  fof(f76,plain,(
% 0.21/0.42    v1_relat_1(sK3)),
% 0.21/0.42    inference(subsumption_resolution,[],[f75,f36])).
% 0.21/0.42  fof(f75,plain,(
% 0.21/0.42    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3)),
% 0.21/0.42    inference(resolution,[],[f29,f32])).
% 0.21/0.42  fof(f187,plain,(
% 0.21/0.42    r1_partfun1(sK2,sK3) | ~v1_relat_1(sK3) | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))),
% 0.21/0.42    inference(duplicate_literal_removal,[],[f185])).
% 0.21/0.42  fof(f185,plain,(
% 0.21/0.42    r1_partfun1(sK2,sK3) | ~v1_relat_1(sK3) | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | r1_partfun1(sK2,sK3)),
% 0.21/0.42    inference(resolution,[],[f148,f27])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    v1_funct_1(sK3)),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f148,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_funct_1(X0) | r1_partfun1(sK2,sK3) | ~v1_relat_1(X0) | k1_funct_1(sK2,sK5(sK2,X0)) = k1_funct_1(sK3,sK5(sK2,X0)) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) | r1_partfun1(sK2,X0)) )),
% 0.21/0.42    inference(subsumption_resolution,[],[f147,f30])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    v1_funct_1(sK2)),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f147,plain,(
% 0.21/0.42    ( ! [X0] : (k1_funct_1(sK2,sK5(sK2,X0)) = k1_funct_1(sK3,sK5(sK2,X0)) | r1_partfun1(sK2,sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) | r1_partfun1(sK2,X0)) )),
% 0.21/0.42    inference(subsumption_resolution,[],[f146,f94])).
% 0.21/0.42  fof(f146,plain,(
% 0.21/0.42    ( ! [X0] : (k1_funct_1(sK2,sK5(sK2,X0)) = k1_funct_1(sK3,sK5(sK2,X0)) | r1_partfun1(sK2,sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) | r1_partfun1(sK2,X0)) )),
% 0.21/0.42    inference(resolution,[],[f93,f34])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | r1_partfun1(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : ((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(flattening,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,axiom,(
% 0.21/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) => (r1_partfun1(X0,X1) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2))))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_partfun1)).
% 0.21/0.42  fof(f93,plain,(
% 0.21/0.42    ( ! [X4] : (~r2_hidden(X4,k1_relat_1(sK2)) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | r1_partfun1(sK2,sK3)) )),
% 0.21/0.42    inference(backward_demodulation,[],[f25,f90])).
% 0.21/0.42  fof(f90,plain,(
% 0.21/0.42    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.21/0.42    inference(resolution,[],[f31,f40])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ( ! [X4] : (~r2_hidden(X4,k1_relset_1(sK0,sK1,sK2)) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | r1_partfun1(sK2,sK3)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f216,plain,(
% 0.21/0.42    ( ! [X0] : (k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) )),
% 0.21/0.42    inference(resolution,[],[f184,f41])).
% 0.21/0.42  fof(f184,plain,(
% 0.21/0.42    ~v4_relat_1(sK2,sK0) | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) | k1_xboole_0 = sK1),
% 0.21/0.42    inference(superposition,[],[f181,f122])).
% 0.21/0.42  fof(f181,plain,(
% 0.21/0.42    ~v4_relat_1(sK2,k1_relat_1(sK3)) | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)),
% 0.21/0.42    inference(subsumption_resolution,[],[f179,f94])).
% 0.21/0.42  fof(f179,plain,(
% 0.21/0.42    k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) | ~v1_relat_1(sK2) | ~v4_relat_1(sK2,k1_relat_1(sK3))),
% 0.21/0.42    inference(resolution,[],[f115,f38])).
% 0.21/0.42  fof(f115,plain,(
% 0.21/0.42    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))),
% 0.21/0.42    inference(subsumption_resolution,[],[f114,f27])).
% 0.21/0.42  fof(f114,plain,(
% 0.21/0.42    k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) | ~v1_funct_1(sK3) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))),
% 0.21/0.42    inference(subsumption_resolution,[],[f113,f76])).
% 0.21/0.42  fof(f113,plain,(
% 0.21/0.42    k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))),
% 0.21/0.42    inference(subsumption_resolution,[],[f112,f30])).
% 0.21/0.42  fof(f112,plain,(
% 0.21/0.42    k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))),
% 0.21/0.42    inference(subsumption_resolution,[],[f111,f94])).
% 0.21/0.42  fof(f111,plain,(
% 0.21/0.42    k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))),
% 0.21/0.42    inference(resolution,[],[f24,f35])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) | r1_partfun1(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  fof(f241,plain,(
% 0.21/0.42    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) | k1_xboole_0 = sK1),
% 0.21/0.42    inference(subsumption_resolution,[],[f240,f27])).
% 0.21/0.42  fof(f240,plain,(
% 0.21/0.42    ~v1_funct_1(sK3) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) | k1_xboole_0 = sK1),
% 0.21/0.42    inference(subsumption_resolution,[],[f239,f76])).
% 0.21/0.42  fof(f239,plain,(
% 0.21/0.42    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) | k1_xboole_0 = sK1),
% 0.21/0.42    inference(duplicate_literal_removal,[],[f233])).
% 0.21/0.42  fof(f233,plain,(
% 0.21/0.42    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.21/0.42    inference(resolution,[],[f229,f227])).
% 0.21/0.42  fof(f227,plain,(
% 0.21/0.42    r1_partfun1(sK2,sK3) | k1_xboole_0 = sK1),
% 0.21/0.42    inference(subsumption_resolution,[],[f225,f219])).
% 0.21/0.42  fof(f225,plain,(
% 0.21/0.42    k1_xboole_0 = sK1 | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) | r1_partfun1(sK2,sK3)),
% 0.21/0.42    inference(resolution,[],[f224,f93])).
% 0.21/0.42  fof(f224,plain,(
% 0.21/0.42    r2_hidden(sK4,k1_relat_1(sK2)) | k1_xboole_0 = sK1),
% 0.21/0.42    inference(subsumption_resolution,[],[f223,f208])).
% 0.21/0.42  fof(f208,plain,(
% 0.21/0.42    r2_hidden(sK4,k1_relat_1(sK2)) | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) | k1_xboole_0 = sK1),
% 0.21/0.42    inference(resolution,[],[f206,f92])).
% 0.21/0.42  fof(f92,plain,(
% 0.21/0.42    ~r1_partfun1(sK2,sK3) | r2_hidden(sK4,k1_relat_1(sK2))),
% 0.21/0.42    inference(backward_demodulation,[],[f23,f90])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) | ~r1_partfun1(sK2,sK3)),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f223,plain,(
% 0.21/0.42    r2_hidden(sK4,k1_relat_1(sK2)) | k1_xboole_0 = sK1 | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))),
% 0.21/0.42    inference(resolution,[],[f175,f31])).
% 0.21/0.42  fof(f175,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | r2_hidden(sK4,k1_relat_1(sK2)) | k1_xboole_0 = sK1 | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))) )),
% 0.21/0.42    inference(resolution,[],[f174,f41])).
% 0.21/0.42  fof(f174,plain,(
% 0.21/0.42    ~v4_relat_1(sK2,sK0) | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) | r2_hidden(sK4,k1_relat_1(sK2)) | k1_xboole_0 = sK1),
% 0.21/0.42    inference(superposition,[],[f171,f122])).
% 0.21/0.42  fof(f171,plain,(
% 0.21/0.42    ~v4_relat_1(sK2,k1_relat_1(sK3)) | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) | r2_hidden(sK4,k1_relat_1(sK2))),
% 0.21/0.42    inference(subsumption_resolution,[],[f169,f94])).
% 0.21/0.42  fof(f169,plain,(
% 0.21/0.42    r2_hidden(sK4,k1_relat_1(sK2)) | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) | ~v1_relat_1(sK2) | ~v4_relat_1(sK2,k1_relat_1(sK3))),
% 0.21/0.42    inference(resolution,[],[f109,f38])).
% 0.21/0.42  fof(f109,plain,(
% 0.21/0.42    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | r2_hidden(sK4,k1_relat_1(sK2)) | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))),
% 0.21/0.42    inference(subsumption_resolution,[],[f108,f27])).
% 0.21/0.42  fof(f108,plain,(
% 0.21/0.42    r2_hidden(sK4,k1_relat_1(sK2)) | ~v1_funct_1(sK3) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))),
% 0.21/0.42    inference(subsumption_resolution,[],[f107,f76])).
% 0.21/0.42  fof(f107,plain,(
% 0.21/0.42    r2_hidden(sK4,k1_relat_1(sK2)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))),
% 0.21/0.42    inference(subsumption_resolution,[],[f106,f30])).
% 0.21/0.42  fof(f106,plain,(
% 0.21/0.42    r2_hidden(sK4,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))),
% 0.21/0.42    inference(subsumption_resolution,[],[f105,f94])).
% 0.21/0.42  fof(f105,plain,(
% 0.21/0.42    r2_hidden(sK4,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))),
% 0.21/0.42    inference(resolution,[],[f92,f35])).
% 0.21/0.42  fof(f229,plain,(
% 0.21/0.42    ( ! [X0] : (~r1_partfun1(sK2,X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) | k1_funct_1(sK2,sK4) = k1_funct_1(X0,sK4) | k1_xboole_0 = sK1) )),
% 0.21/0.42    inference(subsumption_resolution,[],[f228,f30])).
% 0.21/0.42  fof(f228,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = sK1 | ~v1_funct_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) | k1_funct_1(sK2,sK4) = k1_funct_1(X0,sK4) | ~r1_partfun1(sK2,X0)) )),
% 0.21/0.42    inference(subsumption_resolution,[],[f226,f94])).
% 0.21/0.42  fof(f226,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = sK1 | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) | k1_funct_1(sK2,sK4) = k1_funct_1(X0,sK4) | ~r1_partfun1(sK2,X0)) )),
% 0.21/0.42    inference(resolution,[],[f224,f33])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0)) | k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r1_partfun1(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f261,plain,(
% 0.21/0.42    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.21/0.42    inference(backward_demodulation,[],[f31,f258])).
% 0.21/0.42  fof(f504,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 0.21/0.42    inference(resolution,[],[f503,f41])).
% 0.21/0.42  fof(f503,plain,(
% 0.21/0.42    ~v4_relat_1(sK2,k1_xboole_0)),
% 0.21/0.42    inference(subsumption_resolution,[],[f497,f94])).
% 0.21/0.42  fof(f497,plain,(
% 0.21/0.42    ~v1_relat_1(sK2) | ~v4_relat_1(sK2,k1_xboole_0)),
% 0.21/0.42    inference(resolution,[],[f490,f38])).
% 0.21/0.42  fof(f490,plain,(
% 0.21/0.42    ~r1_tarski(k1_relat_1(sK2),k1_xboole_0)),
% 0.21/0.42    inference(forward_demodulation,[],[f489,f282])).
% 0.21/0.42  fof(f282,plain,(
% 0.21/0.42    k1_xboole_0 = k1_relat_1(sK3)),
% 0.21/0.42    inference(backward_demodulation,[],[f269,f281])).
% 0.21/0.42  fof(f281,plain,(
% 0.21/0.42    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 0.21/0.42    inference(subsumption_resolution,[],[f271,f267])).
% 0.21/0.42  fof(f267,plain,(
% 0.21/0.42    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.42    inference(backward_demodulation,[],[f260,f265])).
% 0.21/0.42  fof(f260,plain,(
% 0.21/0.42    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.21/0.42    inference(backward_demodulation,[],[f29,f258])).
% 0.21/0.42  fof(f271,plain,(
% 0.21/0.42    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 0.21/0.42    inference(resolution,[],[f266,f60])).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    ( ! [X8] : (~v1_funct_2(sK3,X8,X8) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X8))) | k1_relset_1(X8,X8,sK3) = X8) )),
% 0.21/0.42    inference(resolution,[],[f27,f39])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.42    inference(flattening,[],[f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.42    inference(ennf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,axiom,(
% 0.21/0.42    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).
% 0.21/0.42  fof(f266,plain,(
% 0.21/0.42    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 0.21/0.42    inference(backward_demodulation,[],[f259,f265])).
% 0.21/0.42  fof(f259,plain,(
% 0.21/0.42    v1_funct_2(sK3,sK0,k1_xboole_0)),
% 0.21/0.42    inference(backward_demodulation,[],[f28,f258])).
% 0.21/0.42  fof(f269,plain,(
% 0.21/0.42    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 0.21/0.42    inference(backward_demodulation,[],[f262,f265])).
% 0.21/0.42  fof(f262,plain,(
% 0.21/0.42    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3)),
% 0.21/0.42    inference(backward_demodulation,[],[f74,f258])).
% 0.21/0.42  fof(f489,plain,(
% 0.21/0.42    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))),
% 0.21/0.42    inference(subsumption_resolution,[],[f488,f76])).
% 0.21/0.42  fof(f488,plain,(
% 0.21/0.42    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 0.21/0.42    inference(subsumption_resolution,[],[f487,f475])).
% 0.21/0.42  fof(f475,plain,(
% 0.21/0.42    k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)),
% 0.21/0.42    inference(subsumption_resolution,[],[f469,f436])).
% 0.21/0.42  fof(f436,plain,(
% 0.21/0.42    k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))),
% 0.21/0.42    inference(resolution,[],[f424,f24])).
% 0.21/0.42  fof(f424,plain,(
% 0.21/0.42    r1_partfun1(sK2,sK3) | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))),
% 0.21/0.42    inference(resolution,[],[f291,f268])).
% 0.21/0.42  fof(f291,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) | r1_partfun1(sK2,sK3)) )),
% 0.21/0.42    inference(backward_demodulation,[],[f193,f282])).
% 0.21/0.42  fof(f193,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) | r1_partfun1(sK2,sK3)) )),
% 0.21/0.42    inference(resolution,[],[f192,f41])).
% 0.21/0.42  fof(f469,plain,(
% 0.21/0.42    k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))),
% 0.21/0.42    inference(resolution,[],[f288,f268])).
% 0.21/0.42  fof(f288,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))) )),
% 0.21/0.42    inference(backward_demodulation,[],[f182,f282])).
% 0.21/0.42  fof(f182,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) | k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))) )),
% 0.21/0.42    inference(resolution,[],[f181,f41])).
% 0.21/0.42  fof(f487,plain,(
% 0.21/0.42    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) | ~v1_relat_1(sK3)),
% 0.21/0.42    inference(subsumption_resolution,[],[f486,f27])).
% 0.21/0.42  fof(f486,plain,(
% 0.21/0.42    ~v1_funct_1(sK3) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) | ~v1_relat_1(sK3)),
% 0.21/0.42    inference(duplicate_literal_removal,[],[f481])).
% 0.21/0.42  fof(f481,plain,(
% 0.21/0.42    ~v1_funct_1(sK3) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) | ~v1_relat_1(sK3) | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)),
% 0.21/0.42    inference(resolution,[],[f468,f465])).
% 0.21/0.42  fof(f465,plain,(
% 0.21/0.42    r1_partfun1(sK2,sK3) | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)),
% 0.21/0.42    inference(resolution,[],[f464,f93])).
% 0.21/0.42  fof(f464,plain,(
% 0.21/0.42    r2_hidden(sK4,k1_relat_1(sK2))),
% 0.21/0.42    inference(subsumption_resolution,[],[f458,f437])).
% 0.21/0.42  fof(f437,plain,(
% 0.21/0.42    r2_hidden(sK4,k1_relat_1(sK2)) | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))),
% 0.21/0.42    inference(resolution,[],[f424,f92])).
% 0.21/0.42  fof(f458,plain,(
% 0.21/0.42    r2_hidden(sK4,k1_relat_1(sK2)) | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))),
% 0.21/0.42    inference(resolution,[],[f286,f268])).
% 0.21/0.42  fof(f286,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | r2_hidden(sK4,k1_relat_1(sK2)) | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))) )),
% 0.21/0.42    inference(backward_demodulation,[],[f172,f282])).
% 0.21/0.42  fof(f172,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) | r2_hidden(sK4,k1_relat_1(sK2)) | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))) )),
% 0.21/0.42    inference(resolution,[],[f171,f41])).
% 0.21/0.42  fof(f468,plain,(
% 0.21/0.42    ( ! [X0] : (~r1_partfun1(sK2,X0) | ~v1_funct_1(X0) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) | k1_funct_1(sK2,sK4) = k1_funct_1(X0,sK4) | ~v1_relat_1(X0)) )),
% 0.21/0.42    inference(subsumption_resolution,[],[f467,f30])).
% 0.21/0.42  fof(f467,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_funct_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) | k1_funct_1(sK2,sK4) = k1_funct_1(X0,sK4) | ~r1_partfun1(sK2,X0)) )),
% 0.21/0.42    inference(subsumption_resolution,[],[f466,f94])).
% 0.21/0.42  fof(f466,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) | k1_funct_1(sK2,sK4) = k1_funct_1(X0,sK4) | ~r1_partfun1(sK2,X0)) )),
% 0.21/0.42    inference(resolution,[],[f464,f33])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (617)------------------------------
% 0.21/0.42  % (617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (617)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (617)Memory used [KB]: 1791
% 0.21/0.42  % (617)Time elapsed: 0.014 s
% 0.21/0.42  % (617)------------------------------
% 0.21/0.42  % (617)------------------------------
% 0.21/0.43  % (603)Success in time 0.067 s
%------------------------------------------------------------------------------
