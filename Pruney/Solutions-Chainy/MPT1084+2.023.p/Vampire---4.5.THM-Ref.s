%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:22 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 348 expanded)
%              Number of leaves         :   13 ( 103 expanded)
%              Depth                    :   30
%              Number of atoms          :  381 (2164 expanded)
%              Number of equality atoms :  127 ( 456 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f149,plain,(
    $false ),
    inference(resolution,[],[f148,f35])).

fof(f35,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))
    & ! [X2] :
        ( k3_funct_2(sK0,sK0,sK1,X2) = X2
        | ~ m1_subset_1(X2,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f26,f25])).

% (20683)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f25,plain,
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

fof(f26,plain,
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t201_funct_2)).

fof(f148,plain,(
    ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f146,f36])).

fof(f36,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f146,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f145,f37])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f145,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f142,f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f142,plain,(
    ~ r2_funct_2(sK0,sK0,sK1,sK1) ),
    inference(backward_demodulation,[],[f39,f140])).

fof(f140,plain,(
    k6_partfun1(sK0) = sK1 ),
    inference(resolution,[],[f138,f47])).

fof(f47,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f138,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | k6_partfun1(sK0) = sK1 ),
    inference(resolution,[],[f133,f37])).

fof(f133,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | k6_partfun1(sK0) = sK1
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f132,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f132,plain,
    ( ~ v1_relat_1(sK1)
    | k6_partfun1(sK0) = sK1 ),
    inference(resolution,[],[f131,f35])).

fof(f131,plain,
    ( ~ v1_funct_1(sK1)
    | k6_partfun1(sK0) = sK1
    | ~ v1_relat_1(sK1) ),
    inference(trivial_inequality_removal,[],[f130])).

fof(f130,plain,
    ( sK2(sK0,sK1) != sK2(sK0,sK1)
    | k6_partfun1(sK0) = sK1
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,
    ( sK2(sK0,sK1) != sK2(sK0,sK1)
    | k6_partfun1(sK0) = sK1
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k6_partfun1(sK0) = sK1 ),
    inference(superposition,[],[f74,f127])).

fof(f127,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | k6_partfun1(sK0) = sK1 ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | k6_partfun1(sK0) = sK1
    | k6_partfun1(sK0) = sK1 ),
    inference(superposition,[],[f118,f123])).

fof(f123,plain,
    ( k1_funct_1(sK1,sK2(sK0,sK1)) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1))
    | k6_partfun1(sK0) = sK1 ),
    inference(resolution,[],[f121,f47])).

fof(f121,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | k6_partfun1(sK0) = sK1
    | k1_funct_1(sK1,sK2(sK0,sK1)) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1)) ),
    inference(resolution,[],[f108,f37])).

fof(f108,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | k1_funct_1(sK1,sK2(sK0,sK1)) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1))
      | k6_partfun1(sK0) = sK1
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f107,f44])).

fof(f107,plain,
    ( ~ v1_relat_1(sK1)
    | k6_partfun1(sK0) = sK1
    | k1_funct_1(sK1,sK2(sK0,sK1)) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1)) ),
    inference(resolution,[],[f99,f35])).

fof(f99,plain,
    ( ~ v1_funct_1(sK1)
    | k1_funct_1(sK1,sK2(sK0,sK1)) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1))
    | k6_partfun1(sK0) = sK1
    | ~ v1_relat_1(sK1) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,
    ( k1_funct_1(sK1,sK2(sK0,sK1)) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1))
    | ~ v1_funct_1(sK1)
    | k6_partfun1(sK0) = sK1
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f94,f75])).

fof(f75,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | k6_partfun1(sK0) = sK1
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f59,f71])).

fof(f71,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(resolution,[],[f70,f35])).

fof(f70,plain,
    ( ~ v1_funct_1(sK1)
    | sK0 = k1_relat_1(sK1) ),
    inference(resolution,[],[f69,f36])).

fof(f69,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | sK0 = k1_relat_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(forward_demodulation,[],[f67,f64])).

fof(f64,plain,(
    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(resolution,[],[f45,f37])).

fof(f45,plain,(
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

fof(f67,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f46,f37])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f59,plain,(
    ! [X1] :
      ( r2_hidden(sK2(k1_relat_1(X1),X1),k1_relat_1(X1))
      | k6_partfun1(k1_relat_1(X1)) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k6_partfun1(X0) = X1
      | r2_hidden(sK2(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f50,f42])).

fof(f42,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

fof(f94,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0)
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f93,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f93,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | ~ v1_funct_1(sK1)
      | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0) ) ),
    inference(resolution,[],[f87,f36])).

fof(f87,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1)
      | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0) ) ),
    inference(resolution,[],[f72,f37])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
      | ~ v1_funct_2(X1,sK0,X2)
      | ~ v1_funct_1(X1)
      | k3_funct_2(sK0,X2,X1,X0) = k1_funct_1(X1,X0) ) ),
    inference(resolution,[],[f43,f34])).

fof(f34,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f118,plain,
    ( sK2(sK0,sK1) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1))
    | k6_partfun1(sK0) = sK1 ),
    inference(resolution,[],[f113,f47])).

fof(f113,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | k6_partfun1(sK0) = sK1
    | sK2(sK0,sK1) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1)) ),
    inference(resolution,[],[f102,f37])).

fof(f102,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | sK2(sK0,sK1) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1))
      | k6_partfun1(sK0) = sK1
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f100,f44])).

fof(f100,plain,
    ( ~ v1_relat_1(sK1)
    | k6_partfun1(sK0) = sK1
    | sK2(sK0,sK1) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1)) ),
    inference(resolution,[],[f84,f35])).

fof(f84,plain,
    ( ~ v1_funct_1(sK1)
    | k6_partfun1(sK0) = sK1
    | ~ v1_relat_1(sK1)
    | sK2(sK0,sK1) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1)) ),
    inference(resolution,[],[f75,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k3_funct_2(sK0,sK0,sK1,X0) = X0 ) ),
    inference(resolution,[],[f52,f38])).

fof(f38,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | k3_funct_2(sK0,sK0,sK1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,
    ( sK2(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | k6_partfun1(sK0) = sK1
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f58,f71])).

fof(f58,plain,(
    ! [X1] :
      ( sK2(k1_relat_1(X1),X1) != k1_funct_1(X1,sK2(k1_relat_1(X1),X1))
      | k6_partfun1(k1_relat_1(X1)) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k6_partfun1(X0) = X1
      | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f51,f42])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f39,plain,(
    ~ r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:02:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (20698)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.51  % (20690)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (20700)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (20681)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (20691)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.24/0.52  % (20681)Refutation found. Thanks to Tanya!
% 1.24/0.52  % SZS status Theorem for theBenchmark
% 1.24/0.52  % SZS output start Proof for theBenchmark
% 1.24/0.52  fof(f149,plain,(
% 1.24/0.52    $false),
% 1.24/0.52    inference(resolution,[],[f148,f35])).
% 1.24/0.52  fof(f35,plain,(
% 1.24/0.52    v1_funct_1(sK1)),
% 1.24/0.52    inference(cnf_transformation,[],[f27])).
% 1.24/0.52  fof(f27,plain,(
% 1.24/0.52    (~r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) & ! [X2] : (k3_funct_2(sK0,sK0,sK1,X2) = X2 | ~m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)) & ~v1_xboole_0(sK0)),
% 1.24/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f26,f25])).
% 1.24/0.52  % (20683)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.24/0.52  fof(f25,plain,(
% 1.24/0.52    ? [X0] : (? [X1] : (~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (~r2_funct_2(sK0,sK0,X1,k6_partfun1(sK0)) & ! [X2] : (k3_funct_2(sK0,sK0,X1,X2) = X2 | ~m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X1,sK0,sK0) & v1_funct_1(X1)) & ~v1_xboole_0(sK0))),
% 1.24/0.52    introduced(choice_axiom,[])).
% 1.24/0.52  fof(f26,plain,(
% 1.24/0.52    ? [X1] : (~r2_funct_2(sK0,sK0,X1,k6_partfun1(sK0)) & ! [X2] : (k3_funct_2(sK0,sK0,X1,X2) = X2 | ~m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X1,sK0,sK0) & v1_funct_1(X1)) => (~r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) & ! [X2] : (k3_funct_2(sK0,sK0,sK1,X2) = X2 | ~m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.24/0.52    introduced(choice_axiom,[])).
% 1.24/0.52  fof(f13,plain,(
% 1.24/0.52    ? [X0] : (? [X1] : (~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0))),
% 1.24/0.52    inference(flattening,[],[f12])).
% 1.24/0.52  fof(f12,plain,(
% 1.24/0.52    ? [X0] : (? [X1] : ((~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))) & ~v1_xboole_0(X0))),
% 1.24/0.52    inference(ennf_transformation,[],[f11])).
% 1.24/0.52  fof(f11,negated_conjecture,(
% 1.24/0.52    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (! [X2] : (m1_subset_1(X2,X0) => k3_funct_2(X0,X0,X1,X2) = X2) => r2_funct_2(X0,X0,X1,k6_partfun1(X0)))))),
% 1.24/0.52    inference(negated_conjecture,[],[f10])).
% 1.24/0.52  fof(f10,conjecture,(
% 1.24/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (! [X2] : (m1_subset_1(X2,X0) => k3_funct_2(X0,X0,X1,X2) = X2) => r2_funct_2(X0,X0,X1,k6_partfun1(X0)))))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t201_funct_2)).
% 1.24/0.52  fof(f148,plain,(
% 1.24/0.52    ~v1_funct_1(sK1)),
% 1.24/0.52    inference(resolution,[],[f146,f36])).
% 1.24/0.52  fof(f36,plain,(
% 1.24/0.52    v1_funct_2(sK1,sK0,sK0)),
% 1.24/0.52    inference(cnf_transformation,[],[f27])).
% 1.24/0.52  fof(f146,plain,(
% 1.24/0.52    ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.24/0.52    inference(resolution,[],[f145,f37])).
% 1.24/0.52  fof(f37,plain,(
% 1.24/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.24/0.52    inference(cnf_transformation,[],[f27])).
% 1.24/0.52  fof(f145,plain,(
% 1.24/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.24/0.52    inference(resolution,[],[f142,f62])).
% 1.24/0.52  fof(f62,plain,(
% 1.24/0.52    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.24/0.52    inference(duplicate_literal_removal,[],[f57])).
% 1.24/0.52  fof(f57,plain,(
% 1.24/0.52    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.24/0.52    inference(equality_resolution,[],[f41])).
% 1.24/0.52  fof(f41,plain,(
% 1.24/0.52    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f28])).
% 1.24/0.52  fof(f28,plain,(
% 1.24/0.52    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.24/0.52    inference(nnf_transformation,[],[f15])).
% 1.24/0.52  fof(f15,plain,(
% 1.24/0.52    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.24/0.52    inference(flattening,[],[f14])).
% 1.24/0.52  fof(f14,plain,(
% 1.24/0.52    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.24/0.52    inference(ennf_transformation,[],[f8])).
% 1.24/0.52  fof(f8,axiom,(
% 1.24/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 1.24/0.52  fof(f142,plain,(
% 1.24/0.52    ~r2_funct_2(sK0,sK0,sK1,sK1)),
% 1.24/0.52    inference(backward_demodulation,[],[f39,f140])).
% 1.24/0.52  fof(f140,plain,(
% 1.24/0.52    k6_partfun1(sK0) = sK1),
% 1.24/0.52    inference(resolution,[],[f138,f47])).
% 1.24/0.52  fof(f47,plain,(
% 1.24/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.24/0.52    inference(cnf_transformation,[],[f3])).
% 1.24/0.52  fof(f3,axiom,(
% 1.24/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.24/0.52  fof(f138,plain,(
% 1.24/0.52    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | k6_partfun1(sK0) = sK1),
% 1.24/0.52    inference(resolution,[],[f133,f37])).
% 1.24/0.52  fof(f133,plain,(
% 1.24/0.52    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | k6_partfun1(sK0) = sK1 | ~v1_relat_1(X0)) )),
% 1.24/0.52    inference(resolution,[],[f132,f44])).
% 1.24/0.52  fof(f44,plain,(
% 1.24/0.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f18])).
% 1.24/0.52  fof(f18,plain,(
% 1.24/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.24/0.52    inference(ennf_transformation,[],[f2])).
% 1.24/0.52  fof(f2,axiom,(
% 1.24/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.24/0.52  fof(f132,plain,(
% 1.24/0.52    ~v1_relat_1(sK1) | k6_partfun1(sK0) = sK1),
% 1.24/0.52    inference(resolution,[],[f131,f35])).
% 1.24/0.52  fof(f131,plain,(
% 1.24/0.52    ~v1_funct_1(sK1) | k6_partfun1(sK0) = sK1 | ~v1_relat_1(sK1)),
% 1.24/0.52    inference(trivial_inequality_removal,[],[f130])).
% 1.24/0.52  fof(f130,plain,(
% 1.24/0.52    sK2(sK0,sK1) != sK2(sK0,sK1) | k6_partfun1(sK0) = sK1 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.24/0.52    inference(duplicate_literal_removal,[],[f129])).
% 1.24/0.52  fof(f129,plain,(
% 1.24/0.52    sK2(sK0,sK1) != sK2(sK0,sK1) | k6_partfun1(sK0) = sK1 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k6_partfun1(sK0) = sK1),
% 1.24/0.52    inference(superposition,[],[f74,f127])).
% 1.24/0.52  fof(f127,plain,(
% 1.24/0.52    sK2(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | k6_partfun1(sK0) = sK1),
% 1.24/0.52    inference(duplicate_literal_removal,[],[f126])).
% 1.24/0.52  fof(f126,plain,(
% 1.24/0.52    sK2(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | k6_partfun1(sK0) = sK1 | k6_partfun1(sK0) = sK1),
% 1.24/0.52    inference(superposition,[],[f118,f123])).
% 1.24/0.52  fof(f123,plain,(
% 1.24/0.52    k1_funct_1(sK1,sK2(sK0,sK1)) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1)) | k6_partfun1(sK0) = sK1),
% 1.24/0.52    inference(resolution,[],[f121,f47])).
% 1.24/0.52  fof(f121,plain,(
% 1.24/0.52    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | k6_partfun1(sK0) = sK1 | k1_funct_1(sK1,sK2(sK0,sK1)) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1))),
% 1.24/0.52    inference(resolution,[],[f108,f37])).
% 1.24/0.52  fof(f108,plain,(
% 1.24/0.52    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | k1_funct_1(sK1,sK2(sK0,sK1)) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1)) | k6_partfun1(sK0) = sK1 | ~v1_relat_1(X0)) )),
% 1.24/0.52    inference(resolution,[],[f107,f44])).
% 1.24/0.52  fof(f107,plain,(
% 1.24/0.52    ~v1_relat_1(sK1) | k6_partfun1(sK0) = sK1 | k1_funct_1(sK1,sK2(sK0,sK1)) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1))),
% 1.24/0.52    inference(resolution,[],[f99,f35])).
% 1.24/0.52  fof(f99,plain,(
% 1.24/0.52    ~v1_funct_1(sK1) | k1_funct_1(sK1,sK2(sK0,sK1)) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1)) | k6_partfun1(sK0) = sK1 | ~v1_relat_1(sK1)),
% 1.24/0.52    inference(duplicate_literal_removal,[],[f98])).
% 1.24/0.52  fof(f98,plain,(
% 1.24/0.52    k1_funct_1(sK1,sK2(sK0,sK1)) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1)) | ~v1_funct_1(sK1) | k6_partfun1(sK0) = sK1 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.24/0.52    inference(resolution,[],[f94,f75])).
% 1.24/0.52  fof(f75,plain,(
% 1.24/0.52    r2_hidden(sK2(sK0,sK1),sK0) | k6_partfun1(sK0) = sK1 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.24/0.52    inference(superposition,[],[f59,f71])).
% 1.24/0.52  fof(f71,plain,(
% 1.24/0.52    sK0 = k1_relat_1(sK1)),
% 1.24/0.52    inference(resolution,[],[f70,f35])).
% 1.24/0.52  fof(f70,plain,(
% 1.24/0.52    ~v1_funct_1(sK1) | sK0 = k1_relat_1(sK1)),
% 1.24/0.52    inference(resolution,[],[f69,f36])).
% 1.24/0.52  fof(f69,plain,(
% 1.24/0.52    ~v1_funct_2(sK1,sK0,sK0) | sK0 = k1_relat_1(sK1) | ~v1_funct_1(sK1)),
% 1.24/0.52    inference(forward_demodulation,[],[f67,f64])).
% 1.24/0.52  fof(f64,plain,(
% 1.24/0.52    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)),
% 1.24/0.52    inference(resolution,[],[f45,f37])).
% 1.24/0.52  fof(f45,plain,(
% 1.24/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f19])).
% 1.24/0.52  fof(f19,plain,(
% 1.24/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/0.52    inference(ennf_transformation,[],[f5])).
% 1.24/0.52  fof(f5,axiom,(
% 1.24/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.24/0.52  fof(f67,plain,(
% 1.24/0.52    sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.24/0.52    inference(resolution,[],[f46,f37])).
% 1.24/0.52  fof(f46,plain,(
% 1.24/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0 | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f21])).
% 1.24/0.52  fof(f21,plain,(
% 1.24/0.52    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.24/0.52    inference(flattening,[],[f20])).
% 1.24/0.52  fof(f20,plain,(
% 1.24/0.52    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.24/0.52    inference(ennf_transformation,[],[f9])).
% 1.24/0.52  fof(f9,axiom,(
% 1.24/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).
% 1.24/0.52  fof(f59,plain,(
% 1.24/0.52    ( ! [X1] : (r2_hidden(sK2(k1_relat_1(X1),X1),k1_relat_1(X1)) | k6_partfun1(k1_relat_1(X1)) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.24/0.52    inference(equality_resolution,[],[f54])).
% 1.24/0.52  fof(f54,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k6_partfun1(X0) = X1 | r2_hidden(sK2(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.24/0.52    inference(definition_unfolding,[],[f50,f42])).
% 1.24/0.52  fof(f42,plain,(
% 1.24/0.52    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f7])).
% 1.24/0.52  fof(f7,axiom,(
% 1.24/0.52    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.24/0.52  fof(f50,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f33])).
% 1.24/0.52  fof(f33,plain,(
% 1.24/0.52    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.24/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 1.24/0.52  fof(f32,plain,(
% 1.24/0.52    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 1.24/0.52    introduced(choice_axiom,[])).
% 1.24/0.52  fof(f31,plain,(
% 1.24/0.52    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.24/0.52    inference(rectify,[],[f30])).
% 1.24/0.52  fof(f30,plain,(
% 1.24/0.52    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.24/0.52    inference(flattening,[],[f29])).
% 1.24/0.52  fof(f29,plain,(
% 1.24/0.52    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.24/0.52    inference(nnf_transformation,[],[f23])).
% 1.24/0.52  fof(f23,plain,(
% 1.24/0.52    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.24/0.52    inference(flattening,[],[f22])).
% 1.24/0.52  fof(f22,plain,(
% 1.24/0.52    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.24/0.52    inference(ennf_transformation,[],[f4])).
% 1.24/0.52  fof(f4,axiom,(
% 1.24/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).
% 1.24/0.52  fof(f94,plain,(
% 1.24/0.52    ( ! [X0] : (~r2_hidden(X0,sK0) | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0) | ~v1_funct_1(sK1)) )),
% 1.24/0.52    inference(resolution,[],[f93,f52])).
% 1.24/0.52  fof(f52,plain,(
% 1.24/0.52    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f24])).
% 1.24/0.52  fof(f24,plain,(
% 1.24/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.24/0.52    inference(ennf_transformation,[],[f1])).
% 1.24/0.52  fof(f1,axiom,(
% 1.24/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.24/0.52  fof(f93,plain,(
% 1.24/0.52    ( ! [X0] : (~m1_subset_1(X0,sK0) | ~v1_funct_1(sK1) | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0)) )),
% 1.24/0.52    inference(resolution,[],[f87,f36])).
% 1.24/0.52  fof(f87,plain,(
% 1.24/0.52    ( ! [X0] : (~m1_subset_1(X0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0)) )),
% 1.24/0.52    inference(resolution,[],[f72,f37])).
% 1.24/0.52  fof(f72,plain,(
% 1.24/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) | ~v1_funct_2(X1,sK0,X2) | ~v1_funct_1(X1) | k3_funct_2(sK0,X2,X1,X0) = k1_funct_1(X1,X0)) )),
% 1.24/0.52    inference(resolution,[],[f43,f34])).
% 1.24/0.52  fof(f34,plain,(
% 1.24/0.52    ~v1_xboole_0(sK0)),
% 1.24/0.52    inference(cnf_transformation,[],[f27])).
% 1.24/0.52  fof(f43,plain,(
% 1.24/0.52    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f17])).
% 1.24/0.52  fof(f17,plain,(
% 1.24/0.52    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.24/0.52    inference(flattening,[],[f16])).
% 1.24/0.52  fof(f16,plain,(
% 1.24/0.52    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.24/0.52    inference(ennf_transformation,[],[f6])).
% 1.24/0.52  fof(f6,axiom,(
% 1.24/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 1.24/0.52  fof(f118,plain,(
% 1.24/0.52    sK2(sK0,sK1) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1)) | k6_partfun1(sK0) = sK1),
% 1.24/0.52    inference(resolution,[],[f113,f47])).
% 1.24/0.52  fof(f113,plain,(
% 1.24/0.52    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | k6_partfun1(sK0) = sK1 | sK2(sK0,sK1) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1))),
% 1.24/0.52    inference(resolution,[],[f102,f37])).
% 1.24/0.52  fof(f102,plain,(
% 1.24/0.52    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | sK2(sK0,sK1) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1)) | k6_partfun1(sK0) = sK1 | ~v1_relat_1(X0)) )),
% 1.24/0.52    inference(resolution,[],[f100,f44])).
% 1.24/0.52  fof(f100,plain,(
% 1.24/0.52    ~v1_relat_1(sK1) | k6_partfun1(sK0) = sK1 | sK2(sK0,sK1) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1))),
% 1.24/0.52    inference(resolution,[],[f84,f35])).
% 1.24/0.52  fof(f84,plain,(
% 1.24/0.52    ~v1_funct_1(sK1) | k6_partfun1(sK0) = sK1 | ~v1_relat_1(sK1) | sK2(sK0,sK1) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1))),
% 1.24/0.52    inference(resolution,[],[f75,f63])).
% 1.24/0.52  fof(f63,plain,(
% 1.24/0.52    ( ! [X0] : (~r2_hidden(X0,sK0) | k3_funct_2(sK0,sK0,sK1,X0) = X0) )),
% 1.24/0.52    inference(resolution,[],[f52,f38])).
% 1.24/0.52  fof(f38,plain,(
% 1.24/0.52    ( ! [X2] : (~m1_subset_1(X2,sK0) | k3_funct_2(sK0,sK0,sK1,X2) = X2) )),
% 1.24/0.52    inference(cnf_transformation,[],[f27])).
% 1.24/0.52  fof(f74,plain,(
% 1.24/0.52    sK2(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1)) | k6_partfun1(sK0) = sK1 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.24/0.52    inference(superposition,[],[f58,f71])).
% 1.24/0.52  fof(f58,plain,(
% 1.24/0.52    ( ! [X1] : (sK2(k1_relat_1(X1),X1) != k1_funct_1(X1,sK2(k1_relat_1(X1),X1)) | k6_partfun1(k1_relat_1(X1)) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.24/0.52    inference(equality_resolution,[],[f53])).
% 1.24/0.52  fof(f53,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k6_partfun1(X0) = X1 | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.24/0.52    inference(definition_unfolding,[],[f51,f42])).
% 1.24/0.52  fof(f51,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f33])).
% 1.24/0.52  fof(f39,plain,(
% 1.24/0.52    ~r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))),
% 1.24/0.52    inference(cnf_transformation,[],[f27])).
% 1.24/0.52  % SZS output end Proof for theBenchmark
% 1.24/0.52  % (20681)------------------------------
% 1.24/0.52  % (20681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.52  % (20681)Termination reason: Refutation
% 1.24/0.52  
% 1.24/0.52  % (20681)Memory used [KB]: 1791
% 1.24/0.52  % (20681)Time elapsed: 0.103 s
% 1.24/0.52  % (20681)------------------------------
% 1.24/0.52  % (20681)------------------------------
% 1.24/0.52  % (20670)Success in time 0.168 s
%------------------------------------------------------------------------------
