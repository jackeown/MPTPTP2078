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
% DateTime   : Thu Dec  3 13:06:48 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 718 expanded)
%              Number of leaves         :   14 ( 218 expanded)
%              Depth                    :   22
%              Number of atoms          :  324 (5672 expanded)
%              Number of equality atoms :   64 (1156 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f197,plain,(
    $false ),
    inference(subsumption_resolution,[],[f194,f110])).

fof(f110,plain,(
    ! [X1] : r2_relset_1(k1_xboole_0,X1,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f106,f89])).

fof(f89,plain,(
    ! [X3] : k1_xboole_0 = sK5(k1_xboole_0,X3) ),
    inference(resolution,[],[f76,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f56,f47])).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f76,plain,(
    ! [X1] : v1_xboole_0(sK5(k1_xboole_0,X1)) ),
    inference(resolution,[],[f72,f70])).

fof(f70,plain,(
    ! [X1] : m1_subset_1(sK5(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f57,f63])).

fof(f63,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f57,plain,(
    ! [X0,X1] : m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK5(X0,X1))
      & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f15,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_1(sK5(X0,X1))
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_1(X2)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_1(X2)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_partfun1)).

fof(f72,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f71,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f60,f47])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f106,plain,(
    ! [X0,X1] : r2_relset_1(X0,X1,sK5(X0,X1),sK5(X0,X1)) ),
    inference(resolution,[],[f64,f57])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f194,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f173,f186])).

fof(f186,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f184,f67])).

fof(f184,plain,(
    v1_xboole_0(sK3) ),
    inference(resolution,[],[f157,f72])).

fof(f157,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f143,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f143,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f43,f138])).

fof(f138,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f133,f104])).

fof(f104,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f64,f40])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_partfun1(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f28,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & r1_partfun1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK0,sK1,sK2,X3)
          & ( k1_xboole_0 = sK0
            | k1_xboole_0 != sK1 )
          & r1_partfun1(sK2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X3)
        & ( k1_xboole_0 = sK0
          | k1_xboole_0 != sK1 )
        & r1_partfun1(sK2,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_partfun1(sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_relset_1(X0,X1,X2,X3)
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_relset_1(X0,X1,X2,X3)
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).

fof(f133,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f46,f126])).

fof(f126,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f124,f67])).

fof(f124,plain,
    ( v1_xboole_0(sK1)
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f122,f40])).

fof(f122,plain,
    ( sK2 = sK3
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f121,f43])).

fof(f121,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | sK2 = sK3
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f120,f114])).

fof(f114,plain,
    ( v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f113,f40])).

fof(f113,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f111,f38])).

fof(f38,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f111,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f51,f39])).

fof(f39,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f120,plain,(
    ! [X0] :
      ( sK2 = sK3
      | ~ v1_partfun1(sK2,sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f119,f116])).

fof(f116,plain,
    ( v1_partfun1(sK3,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f115,f43])).

fof(f115,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f112,f41])).

fof(f41,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f112,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f51,f42])).

fof(f42,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(sK3,X0)
      | sK2 = sK3
      | ~ v1_partfun1(sK2,X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f118,f38])).

fof(f118,plain,(
    ! [X0,X1] :
      ( sK2 = sK3
      | ~ v1_partfun1(sK3,X0)
      | ~ v1_partfun1(sK2,X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f117,f41])).

fof(f117,plain,(
    ! [X0,X1] :
      ( sK2 = sK3
      | ~ v1_partfun1(sK3,X0)
      | ~ v1_partfun1(sK2,X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f59,f44])).

fof(f44,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_partfun1(X2,X3)
      | X2 = X3
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

fof(f46,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f173,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f158,f165])).

fof(f165,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f163,f67])).

fof(f163,plain,(
    v1_xboole_0(sK2) ),
    inference(resolution,[],[f155,f72])).

fof(f155,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f141,f62])).

fof(f141,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f40,f138])).

fof(f158,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK3) ),
    inference(forward_demodulation,[],[f144,f139])).

fof(f139,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f45,f138])).

fof(f45,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f29])).

fof(f144,plain,(
    ~ r2_relset_1(sK0,k1_xboole_0,sK2,sK3) ),
    inference(backward_demodulation,[],[f46,f138])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:51:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (797769728)
% 0.13/0.37  ipcrm: permission denied for id (797802497)
% 0.13/0.37  ipcrm: permission denied for id (797835268)
% 0.13/0.37  ipcrm: permission denied for id (801505285)
% 0.13/0.38  ipcrm: permission denied for id (797868038)
% 0.21/0.38  ipcrm: permission denied for id (797900808)
% 0.21/0.38  ipcrm: permission denied for id (797933577)
% 0.21/0.38  ipcrm: permission denied for id (797966346)
% 0.21/0.38  ipcrm: permission denied for id (798031884)
% 0.21/0.39  ipcrm: permission denied for id (798097422)
% 0.21/0.39  ipcrm: permission denied for id (798130192)
% 0.21/0.39  ipcrm: permission denied for id (801701906)
% 0.21/0.39  ipcrm: permission denied for id (801734675)
% 0.21/0.39  ipcrm: permission denied for id (798228500)
% 0.21/0.39  ipcrm: permission denied for id (798261269)
% 0.21/0.40  ipcrm: permission denied for id (798294038)
% 0.21/0.40  ipcrm: permission denied for id (798326807)
% 0.21/0.40  ipcrm: permission denied for id (798359576)
% 0.21/0.40  ipcrm: permission denied for id (798392345)
% 0.21/0.40  ipcrm: permission denied for id (798425114)
% 0.21/0.40  ipcrm: permission denied for id (798457883)
% 0.21/0.41  ipcrm: permission denied for id (801832990)
% 0.21/0.42  ipcrm: permission denied for id (802095141)
% 0.21/0.42  ipcrm: permission denied for id (802127910)
% 0.21/0.42  ipcrm: permission denied for id (802193448)
% 0.21/0.42  ipcrm: permission denied for id (798720041)
% 0.21/0.42  ipcrm: permission denied for id (798752810)
% 0.21/0.42  ipcrm: permission denied for id (798785579)
% 0.21/0.42  ipcrm: permission denied for id (798818348)
% 0.21/0.43  ipcrm: permission denied for id (798851117)
% 0.21/0.43  ipcrm: permission denied for id (798883886)
% 0.21/0.43  ipcrm: permission denied for id (798916655)
% 0.21/0.43  ipcrm: permission denied for id (798982193)
% 0.21/0.43  ipcrm: permission denied for id (799047731)
% 0.21/0.43  ipcrm: permission denied for id (802291764)
% 0.21/0.44  ipcrm: permission denied for id (799113269)
% 0.21/0.44  ipcrm: permission denied for id (802357303)
% 0.21/0.44  ipcrm: permission denied for id (799211576)
% 0.21/0.44  ipcrm: permission denied for id (802422842)
% 0.21/0.45  ipcrm: permission denied for id (802586687)
% 0.21/0.45  ipcrm: permission denied for id (799473728)
% 0.21/0.45  ipcrm: permission denied for id (802717764)
% 0.21/0.46  ipcrm: permission denied for id (802750533)
% 0.21/0.46  ipcrm: permission denied for id (802783302)
% 0.21/0.46  ipcrm: permission denied for id (802816071)
% 0.21/0.46  ipcrm: permission denied for id (799703113)
% 0.21/0.46  ipcrm: permission denied for id (802881610)
% 0.21/0.46  ipcrm: permission denied for id (799768651)
% 0.21/0.46  ipcrm: permission denied for id (799834188)
% 0.21/0.47  ipcrm: permission denied for id (799899726)
% 0.21/0.47  ipcrm: permission denied for id (799998034)
% 0.21/0.47  ipcrm: permission denied for id (800063573)
% 0.21/0.48  ipcrm: permission denied for id (800096342)
% 0.21/0.48  ipcrm: permission denied for id (800129111)
% 0.21/0.48  ipcrm: permission denied for id (800194649)
% 0.21/0.48  ipcrm: permission denied for id (803143770)
% 0.21/0.48  ipcrm: permission denied for id (803176539)
% 0.21/0.48  ipcrm: permission denied for id (800325725)
% 0.21/0.49  ipcrm: permission denied for id (800391263)
% 0.21/0.49  ipcrm: permission denied for id (803274848)
% 0.21/0.49  ipcrm: permission denied for id (800456801)
% 0.21/0.49  ipcrm: permission denied for id (800489570)
% 0.21/0.49  ipcrm: permission denied for id (800555108)
% 0.21/0.49  ipcrm: permission denied for id (800587877)
% 0.21/0.50  ipcrm: permission denied for id (800620646)
% 0.21/0.50  ipcrm: permission denied for id (800653415)
% 0.21/0.50  ipcrm: permission denied for id (800718952)
% 0.21/0.50  ipcrm: permission denied for id (803340393)
% 0.21/0.50  ipcrm: permission denied for id (800817259)
% 0.21/0.50  ipcrm: permission denied for id (800850028)
% 0.21/0.50  ipcrm: permission denied for id (800882797)
% 0.21/0.51  ipcrm: permission denied for id (800981104)
% 0.21/0.51  ipcrm: permission denied for id (803504242)
% 0.21/0.51  ipcrm: permission denied for id (801144947)
% 0.21/0.51  ipcrm: permission denied for id (801177716)
% 0.21/0.51  ipcrm: permission denied for id (803537013)
% 0.21/0.52  ipcrm: permission denied for id (803602551)
% 0.21/0.52  ipcrm: permission denied for id (801243256)
% 0.21/0.52  ipcrm: permission denied for id (801276026)
% 0.21/0.52  ipcrm: permission denied for id (803668091)
% 0.21/0.53  ipcrm: permission denied for id (801374334)
% 0.38/0.66  % (7940)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.38/0.67  % (7948)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.38/0.67  % (7934)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.38/0.67  % (7944)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.38/0.67  % (7934)Refutation found. Thanks to Tanya!
% 0.38/0.67  % SZS status Theorem for theBenchmark
% 0.38/0.68  % (7932)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.38/0.68  % (7946)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.38/0.68  % (7952)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.38/0.68  % (7936)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.38/0.68  % (7943)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.38/0.68  % (7954)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.38/0.68  % (7956)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.38/0.68  % (7953)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.38/0.68  % (7938)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.38/0.69  % (7945)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.38/0.69  % (7931)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.38/0.69  % SZS output start Proof for theBenchmark
% 0.38/0.69  fof(f197,plain,(
% 0.38/0.69    $false),
% 0.38/0.69    inference(subsumption_resolution,[],[f194,f110])).
% 0.38/0.69  fof(f110,plain,(
% 0.38/0.69    ( ! [X1] : (r2_relset_1(k1_xboole_0,X1,k1_xboole_0,k1_xboole_0)) )),
% 0.38/0.69    inference(superposition,[],[f106,f89])).
% 0.38/0.69  fof(f89,plain,(
% 0.38/0.69    ( ! [X3] : (k1_xboole_0 = sK5(k1_xboole_0,X3)) )),
% 0.38/0.69    inference(resolution,[],[f76,f67])).
% 0.38/0.69  fof(f67,plain,(
% 0.38/0.69    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.38/0.69    inference(resolution,[],[f56,f47])).
% 0.38/0.69  fof(f47,plain,(
% 0.38/0.69    v1_xboole_0(k1_xboole_0)),
% 0.38/0.69    inference(cnf_transformation,[],[f2])).
% 0.38/0.69  fof(f2,axiom,(
% 0.38/0.69    v1_xboole_0(k1_xboole_0)),
% 0.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.38/0.69  fof(f56,plain,(
% 0.38/0.69    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 0.38/0.69    inference(cnf_transformation,[],[f21])).
% 0.38/0.69  fof(f21,plain,(
% 0.38/0.69    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.38/0.69    inference(ennf_transformation,[],[f3])).
% 0.38/0.69  fof(f3,axiom,(
% 0.38/0.69    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.38/0.69  fof(f76,plain,(
% 0.38/0.69    ( ! [X1] : (v1_xboole_0(sK5(k1_xboole_0,X1))) )),
% 0.38/0.69    inference(resolution,[],[f72,f70])).
% 0.38/0.69  fof(f70,plain,(
% 0.38/0.69    ( ! [X1] : (m1_subset_1(sK5(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))) )),
% 0.38/0.69    inference(superposition,[],[f57,f63])).
% 0.38/0.69  fof(f63,plain,(
% 0.38/0.69    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.38/0.69    inference(equality_resolution,[],[f54])).
% 0.38/0.69  fof(f54,plain,(
% 0.38/0.69    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.38/0.69    inference(cnf_transformation,[],[f35])).
% 0.38/0.69  fof(f35,plain,(
% 0.38/0.69    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.38/0.69    inference(flattening,[],[f34])).
% 0.38/0.69  fof(f34,plain,(
% 0.38/0.69    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.38/0.69    inference(nnf_transformation,[],[f5])).
% 0.38/0.69  fof(f5,axiom,(
% 0.38/0.69    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.38/0.69  fof(f57,plain,(
% 0.38/0.69    ( ! [X0,X1] : (m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.38/0.69    inference(cnf_transformation,[],[f37])).
% 0.38/0.69  fof(f37,plain,(
% 0.38/0.69    ! [X0,X1] : (v1_funct_1(sK5(X0,X1)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.38/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f15,f36])).
% 0.38/0.69  fof(f36,plain,(
% 0.38/0.69    ! [X1,X0] : (? [X2] : (v1_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_1(sK5(X0,X1)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.38/0.69    introduced(choice_axiom,[])).
% 0.38/0.69  fof(f15,plain,(
% 0.38/0.69    ! [X0,X1] : ? [X2] : (v1_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.38/0.69    inference(pure_predicate_removal,[],[f14])).
% 0.38/0.69  fof(f14,plain,(
% 0.38/0.69    ! [X0,X1] : ? [X2] : (v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.38/0.69    inference(pure_predicate_removal,[],[f13])).
% 0.38/0.69  fof(f13,plain,(
% 0.38/0.69    ! [X0,X1] : ? [X2] : (v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.38/0.69    inference(pure_predicate_removal,[],[f9])).
% 0.38/0.69  fof(f9,axiom,(
% 0.38/0.69    ! [X0,X1] : ? [X2] : (v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_partfun1)).
% 0.38/0.69  fof(f72,plain,(
% 0.38/0.69    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) )),
% 0.38/0.69    inference(resolution,[],[f71,f49])).
% 0.38/0.69  fof(f49,plain,(
% 0.38/0.69    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 0.38/0.69    inference(cnf_transformation,[],[f33])).
% 0.38/0.69  fof(f33,plain,(
% 0.38/0.69    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.38/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).
% 0.38/0.69  fof(f32,plain,(
% 0.38/0.69    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.38/0.69    introduced(choice_axiom,[])).
% 0.38/0.69  fof(f31,plain,(
% 0.38/0.69    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.38/0.69    inference(rectify,[],[f30])).
% 0.38/0.69  fof(f30,plain,(
% 0.38/0.69    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.38/0.69    inference(nnf_transformation,[],[f1])).
% 0.38/0.69  fof(f1,axiom,(
% 0.38/0.69    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.38/0.69  fof(f71,plain,(
% 0.38/0.69    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) )),
% 0.38/0.69    inference(resolution,[],[f60,f47])).
% 0.38/0.69  fof(f60,plain,(
% 0.38/0.69    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.38/0.69    inference(cnf_transformation,[],[f24])).
% 0.38/0.69  fof(f24,plain,(
% 0.38/0.69    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.38/0.69    inference(ennf_transformation,[],[f6])).
% 0.38/0.69  fof(f6,axiom,(
% 0.38/0.69    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.38/0.69  fof(f106,plain,(
% 0.38/0.69    ( ! [X0,X1] : (r2_relset_1(X0,X1,sK5(X0,X1),sK5(X0,X1))) )),
% 0.38/0.69    inference(resolution,[],[f64,f57])).
% 0.38/0.69  fof(f64,plain,(
% 0.38/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 0.38/0.69    inference(condensation,[],[f61])).
% 0.38/0.69  fof(f61,plain,(
% 0.38/0.69    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.38/0.69    inference(cnf_transformation,[],[f26])).
% 0.38/0.69  fof(f26,plain,(
% 0.38/0.69    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.38/0.69    inference(flattening,[],[f25])).
% 0.38/0.69  fof(f25,plain,(
% 0.38/0.69    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.38/0.69    inference(ennf_transformation,[],[f7])).
% 0.38/0.69  fof(f7,axiom,(
% 0.38/0.69    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.38/0.69  fof(f194,plain,(
% 0.38/0.69    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.38/0.69    inference(backward_demodulation,[],[f173,f186])).
% 0.38/0.69  fof(f186,plain,(
% 0.38/0.69    k1_xboole_0 = sK3),
% 0.38/0.69    inference(resolution,[],[f184,f67])).
% 0.38/0.69  fof(f184,plain,(
% 0.38/0.69    v1_xboole_0(sK3)),
% 0.38/0.69    inference(resolution,[],[f157,f72])).
% 0.38/0.69  fof(f157,plain,(
% 0.38/0.69    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.38/0.69    inference(forward_demodulation,[],[f143,f62])).
% 0.38/0.69  fof(f62,plain,(
% 0.38/0.69    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.38/0.69    inference(equality_resolution,[],[f55])).
% 0.38/0.69  fof(f55,plain,(
% 0.38/0.69    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.38/0.69    inference(cnf_transformation,[],[f35])).
% 0.38/0.69  fof(f143,plain,(
% 0.38/0.69    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.38/0.69    inference(backward_demodulation,[],[f43,f138])).
% 0.38/0.69  fof(f138,plain,(
% 0.38/0.69    k1_xboole_0 = sK1),
% 0.38/0.69    inference(subsumption_resolution,[],[f133,f104])).
% 0.38/0.69  fof(f104,plain,(
% 0.38/0.69    r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.38/0.69    inference(resolution,[],[f64,f40])).
% 0.38/0.69  fof(f40,plain,(
% 0.38/0.69    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.38/0.69    inference(cnf_transformation,[],[f29])).
% 0.38/0.69  fof(f29,plain,(
% 0.38/0.69    (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.38/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f28,f27])).
% 0.38/0.69  fof(f27,plain,(
% 0.38/0.69    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.38/0.69    introduced(choice_axiom,[])).
% 0.38/0.69  fof(f28,plain,(
% 0.38/0.69    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.38/0.69    introduced(choice_axiom,[])).
% 0.38/0.69  fof(f17,plain,(
% 0.38/0.69    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.38/0.69    inference(flattening,[],[f16])).
% 0.38/0.69  fof(f16,plain,(
% 0.38/0.69    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.38/0.69    inference(ennf_transformation,[],[f12])).
% 0.38/0.69  fof(f12,negated_conjecture,(
% 0.38/0.69    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.38/0.69    inference(negated_conjecture,[],[f11])).
% 0.38/0.69  fof(f11,conjecture,(
% 0.38/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).
% 0.38/0.69  fof(f133,plain,(
% 0.38/0.69    ~r2_relset_1(sK0,sK1,sK2,sK2) | k1_xboole_0 = sK1),
% 0.38/0.69    inference(superposition,[],[f46,f126])).
% 0.38/0.69  fof(f126,plain,(
% 0.38/0.69    sK2 = sK3 | k1_xboole_0 = sK1),
% 0.38/0.69    inference(resolution,[],[f124,f67])).
% 0.38/0.69  fof(f124,plain,(
% 0.38/0.69    v1_xboole_0(sK1) | sK2 = sK3),
% 0.38/0.69    inference(subsumption_resolution,[],[f122,f40])).
% 0.38/0.69  fof(f122,plain,(
% 0.38/0.69    sK2 = sK3 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK1)),
% 0.38/0.69    inference(resolution,[],[f121,f43])).
% 0.38/0.69  fof(f121,plain,(
% 0.38/0.69    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | sK2 = sK3 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | v1_xboole_0(sK1)) )),
% 0.38/0.69    inference(subsumption_resolution,[],[f120,f114])).
% 0.38/0.69  fof(f114,plain,(
% 0.38/0.69    v1_partfun1(sK2,sK0) | v1_xboole_0(sK1)),
% 0.38/0.69    inference(subsumption_resolution,[],[f113,f40])).
% 0.38/0.69  fof(f113,plain,(
% 0.38/0.69    v1_partfun1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK1)),
% 0.38/0.69    inference(subsumption_resolution,[],[f111,f38])).
% 0.38/0.69  fof(f38,plain,(
% 0.38/0.69    v1_funct_1(sK2)),
% 0.38/0.69    inference(cnf_transformation,[],[f29])).
% 0.38/0.69  fof(f111,plain,(
% 0.38/0.69    v1_partfun1(sK2,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK1)),
% 0.38/0.69    inference(resolution,[],[f51,f39])).
% 0.38/0.69  fof(f39,plain,(
% 0.38/0.69    v1_funct_2(sK2,sK0,sK1)),
% 0.38/0.69    inference(cnf_transformation,[],[f29])).
% 0.38/0.69  fof(f51,plain,(
% 0.38/0.69    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.38/0.69    inference(cnf_transformation,[],[f19])).
% 0.38/0.69  fof(f19,plain,(
% 0.38/0.69    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.38/0.69    inference(flattening,[],[f18])).
% 0.38/0.69  fof(f18,plain,(
% 0.38/0.69    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.38/0.69    inference(ennf_transformation,[],[f8])).
% 0.38/0.69  fof(f8,axiom,(
% 0.38/0.69    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.38/0.69  fof(f120,plain,(
% 0.38/0.69    ( ! [X0] : (sK2 = sK3 | ~v1_partfun1(sK2,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | v1_xboole_0(sK1)) )),
% 0.38/0.69    inference(resolution,[],[f119,f116])).
% 0.38/0.69  fof(f116,plain,(
% 0.38/0.69    v1_partfun1(sK3,sK0) | v1_xboole_0(sK1)),
% 0.38/0.69    inference(subsumption_resolution,[],[f115,f43])).
% 0.38/0.69  fof(f115,plain,(
% 0.38/0.69    v1_partfun1(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK1)),
% 0.38/0.69    inference(subsumption_resolution,[],[f112,f41])).
% 0.38/0.69  fof(f41,plain,(
% 0.38/0.69    v1_funct_1(sK3)),
% 0.38/0.69    inference(cnf_transformation,[],[f29])).
% 0.38/0.69  fof(f112,plain,(
% 0.38/0.69    v1_partfun1(sK3,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK1)),
% 0.38/0.69    inference(resolution,[],[f51,f42])).
% 0.38/0.69  fof(f42,plain,(
% 0.38/0.69    v1_funct_2(sK3,sK0,sK1)),
% 0.38/0.69    inference(cnf_transformation,[],[f29])).
% 0.38/0.69  fof(f119,plain,(
% 0.38/0.69    ( ! [X0,X1] : (~v1_partfun1(sK3,X0) | sK2 = sK3 | ~v1_partfun1(sK2,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.38/0.69    inference(subsumption_resolution,[],[f118,f38])).
% 0.38/0.69  fof(f118,plain,(
% 0.38/0.69    ( ! [X0,X1] : (sK2 = sK3 | ~v1_partfun1(sK3,X0) | ~v1_partfun1(sK2,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK2)) )),
% 0.38/0.69    inference(subsumption_resolution,[],[f117,f41])).
% 0.38/0.69  fof(f117,plain,(
% 0.38/0.69    ( ! [X0,X1] : (sK2 = sK3 | ~v1_partfun1(sK3,X0) | ~v1_partfun1(sK2,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK2)) )),
% 0.38/0.69    inference(resolution,[],[f59,f44])).
% 0.38/0.69  fof(f44,plain,(
% 0.38/0.69    r1_partfun1(sK2,sK3)),
% 0.38/0.69    inference(cnf_transformation,[],[f29])).
% 0.38/0.69  fof(f59,plain,(
% 0.38/0.69    ( ! [X2,X0,X3,X1] : (~r1_partfun1(X2,X3) | X2 = X3 | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.38/0.69    inference(cnf_transformation,[],[f23])).
% 0.38/0.69  fof(f23,plain,(
% 0.38/0.69    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.38/0.69    inference(flattening,[],[f22])).
% 0.38/0.69  fof(f22,plain,(
% 0.38/0.69    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.38/0.69    inference(ennf_transformation,[],[f10])).
% 0.38/0.69  fof(f10,axiom,(
% 0.38/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 0.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).
% 0.38/0.69  fof(f46,plain,(
% 0.38/0.69    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.38/0.69    inference(cnf_transformation,[],[f29])).
% 0.38/0.69  fof(f43,plain,(
% 0.38/0.69    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.38/0.69    inference(cnf_transformation,[],[f29])).
% 0.38/0.69  fof(f173,plain,(
% 0.38/0.69    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK3)),
% 0.38/0.69    inference(backward_demodulation,[],[f158,f165])).
% 0.38/0.69  fof(f165,plain,(
% 0.38/0.69    k1_xboole_0 = sK2),
% 0.38/0.69    inference(resolution,[],[f163,f67])).
% 0.38/0.69  fof(f163,plain,(
% 0.38/0.69    v1_xboole_0(sK2)),
% 0.38/0.69    inference(resolution,[],[f155,f72])).
% 0.38/0.69  fof(f155,plain,(
% 0.38/0.69    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.38/0.69    inference(forward_demodulation,[],[f141,f62])).
% 0.38/0.69  fof(f141,plain,(
% 0.38/0.69    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.38/0.69    inference(backward_demodulation,[],[f40,f138])).
% 0.38/0.69  fof(f158,plain,(
% 0.38/0.69    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK3)),
% 0.38/0.69    inference(forward_demodulation,[],[f144,f139])).
% 0.38/0.69  fof(f139,plain,(
% 0.38/0.69    k1_xboole_0 = sK0),
% 0.38/0.69    inference(subsumption_resolution,[],[f45,f138])).
% 0.38/0.69  fof(f45,plain,(
% 0.38/0.69    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.38/0.69    inference(cnf_transformation,[],[f29])).
% 0.38/0.69  fof(f144,plain,(
% 0.38/0.69    ~r2_relset_1(sK0,k1_xboole_0,sK2,sK3)),
% 0.38/0.69    inference(backward_demodulation,[],[f46,f138])).
% 0.38/0.69  % SZS output end Proof for theBenchmark
% 0.38/0.69  % (7934)------------------------------
% 0.38/0.69  % (7934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.69  % (7934)Termination reason: Refutation
% 0.38/0.69  
% 0.38/0.69  % (7934)Memory used [KB]: 6268
% 0.38/0.69  % (7934)Time elapsed: 0.088 s
% 0.38/0.69  % (7934)------------------------------
% 0.38/0.69  % (7934)------------------------------
% 0.38/0.69  % (7933)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.38/0.69  % (7944)Refutation not found, incomplete strategy% (7944)------------------------------
% 0.38/0.69  % (7944)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.69  % (7745)Success in time 0.327 s
%------------------------------------------------------------------------------
