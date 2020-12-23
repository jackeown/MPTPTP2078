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
% DateTime   : Thu Dec  3 13:08:20 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 665 expanded)
%              Number of leaves         :   13 ( 200 expanded)
%              Depth                    :   31
%              Number of atoms          :  361 (4199 expanded)
%              Number of equality atoms :   95 ( 695 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f163,plain,(
    $false ),
    inference(subsumption_resolution,[],[f162,f37])).

fof(f37,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

% (2466)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f29,plain,
    ( ~ r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))
    & ! [X2] :
        ( k3_funct_2(sK0,sK0,sK1,X2) = X2
        | ~ m1_subset_1(X2,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f28,f27])).

fof(f27,plain,
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

fof(f28,plain,
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

fof(f162,plain,(
    ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f161,f38])).

fof(f38,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f161,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f159,f39])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f159,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(X0,sK0,sK0)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f158,f37])).

fof(f158,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(X0,sK0,sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f157,f38])).

fof(f157,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(X0,sK0,sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f156,f39])).

fof(f156,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(X0,sK0,sK0)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f147,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(f147,plain,(
    ~ r2_funct_2(sK0,sK0,sK1,sK1) ),
    inference(backward_demodulation,[],[f62,f146])).

fof(f146,plain,(
    sK1 = k6_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f145,f119])).

fof(f119,plain,
    ( m1_subset_1(sK2(sK0,sK1),sK0)
    | sK1 = k6_relat_1(sK0) ),
    inference(resolution,[],[f107,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f107,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | sK1 = k6_relat_1(sK0) ),
    inference(forward_demodulation,[],[f106,f100])).

fof(f100,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f99,f90])).

fof(f90,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f39,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f99,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f98,f84])).

fof(f84,plain,(
    v1_partfun1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f83,f36])).

fof(f36,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f83,plain,
    ( v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f82,f39])).

fof(f82,plain,
    ( v1_partfun1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f74,f37])).

fof(f74,plain,
    ( v1_partfun1(sK1,sK0)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f38,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f98,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f89,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f89,plain,(
    v4_relat_1(sK1,sK0) ),
    inference(resolution,[],[f39,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f106,plain,
    ( sK1 = k6_relat_1(sK0)
    | r2_hidden(sK2(k1_relat_1(sK1),sK1),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f101,f90])).

fof(f101,plain,
    ( sK1 = k6_relat_1(sK0)
    | r2_hidden(sK2(k1_relat_1(sK1),sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(backward_demodulation,[],[f68,f100])).

fof(f68,plain,
    ( sK1 = k6_relat_1(k1_relat_1(sK1))
    | r2_hidden(sK2(k1_relat_1(sK1),sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f37,f58])).

fof(f58,plain,(
    ! [X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | r2_hidden(sK2(k1_relat_1(X1),X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

fof(f145,plain,
    ( sK1 = k6_relat_1(sK0)
    | ~ m1_subset_1(sK2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f144,f109])).

fof(f109,plain,
    ( sK2(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1))
    | sK1 = k6_relat_1(sK0) ),
    inference(forward_demodulation,[],[f108,f100])).

fof(f108,plain,
    ( sK1 = k6_relat_1(sK0)
    | sK2(k1_relat_1(sK1),sK1) != k1_funct_1(sK1,sK2(k1_relat_1(sK1),sK1)) ),
    inference(subsumption_resolution,[],[f102,f90])).

fof(f102,plain,
    ( sK1 = k6_relat_1(sK0)
    | sK2(k1_relat_1(sK1),sK1) != k1_funct_1(sK1,sK2(k1_relat_1(sK1),sK1))
    | ~ v1_relat_1(sK1) ),
    inference(backward_demodulation,[],[f69,f100])).

fof(f69,plain,
    ( sK1 = k6_relat_1(k1_relat_1(sK1))
    | sK2(k1_relat_1(sK1),sK1) != k1_funct_1(sK1,sK2(k1_relat_1(sK1),sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f37,f57])).

fof(f57,plain,(
    ! [X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | sK2(k1_relat_1(X1),X1) != k1_funct_1(X1,sK2(k1_relat_1(X1),X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f144,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | sK1 = k6_relat_1(sK0)
    | ~ m1_subset_1(sK2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f143,f36])).

fof(f143,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | sK1 = k6_relat_1(sK0)
    | ~ m1_subset_1(sK2(sK0,sK1),sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f142,f37])).

fof(f142,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | sK1 = k6_relat_1(sK0)
    | ~ m1_subset_1(sK2(sK0,sK1),sK0)
    | ~ v1_funct_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f141,f38])).

fof(f141,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | sK1 = k6_relat_1(sK0)
    | ~ m1_subset_1(sK2(sK0,sK1),sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f139,f39])).

fof(f139,plain,
    ( sK2(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | sK1 = k6_relat_1(sK0)
    | ~ m1_subset_1(sK2(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v1_xboole_0(sK0) ),
    inference(superposition,[],[f127,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f127,plain,
    ( sK2(sK0,sK1) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1))
    | sK1 = k6_relat_1(sK0) ),
    inference(resolution,[],[f40,f119])).

fof(f40,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | k3_funct_2(sK0,sK0,sK1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    ~ r2_funct_2(sK0,sK0,sK1,k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f41,f42])).

fof(f42,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f41,plain,(
    ~ r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f29])).
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
% 0.14/0.35  % DateTime   : Tue Dec  1 18:14:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (2470)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (2470)Refutation not found, incomplete strategy% (2470)------------------------------
% 0.22/0.52  % (2470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (2478)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (2470)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (2470)Memory used [KB]: 6140
% 0.22/0.52  % (2470)Time elapsed: 0.006 s
% 0.22/0.52  % (2470)------------------------------
% 0.22/0.52  % (2470)------------------------------
% 0.22/0.52  % (2462)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.22/0.52  % (2459)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.22/0.53  % (2463)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.22/0.53  % (2478)Refutation found. Thanks to Tanya!
% 1.22/0.53  % SZS status Theorem for theBenchmark
% 1.22/0.53  % SZS output start Proof for theBenchmark
% 1.22/0.53  fof(f163,plain,(
% 1.22/0.53    $false),
% 1.22/0.53    inference(subsumption_resolution,[],[f162,f37])).
% 1.22/0.53  fof(f37,plain,(
% 1.22/0.53    v1_funct_1(sK1)),
% 1.22/0.53    inference(cnf_transformation,[],[f29])).
% 1.22/0.53  % (2466)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.22/0.53  fof(f29,plain,(
% 1.22/0.53    (~r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) & ! [X2] : (k3_funct_2(sK0,sK0,sK1,X2) = X2 | ~m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)) & ~v1_xboole_0(sK0)),
% 1.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f28,f27])).
% 1.22/0.53  fof(f27,plain,(
% 1.22/0.53    ? [X0] : (? [X1] : (~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (~r2_funct_2(sK0,sK0,X1,k6_partfun1(sK0)) & ! [X2] : (k3_funct_2(sK0,sK0,X1,X2) = X2 | ~m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X1,sK0,sK0) & v1_funct_1(X1)) & ~v1_xboole_0(sK0))),
% 1.22/0.53    introduced(choice_axiom,[])).
% 1.22/0.53  fof(f28,plain,(
% 1.22/0.53    ? [X1] : (~r2_funct_2(sK0,sK0,X1,k6_partfun1(sK0)) & ! [X2] : (k3_funct_2(sK0,sK0,X1,X2) = X2 | ~m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X1,sK0,sK0) & v1_funct_1(X1)) => (~r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) & ! [X2] : (k3_funct_2(sK0,sK0,sK1,X2) = X2 | ~m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.22/0.53    introduced(choice_axiom,[])).
% 1.22/0.53  fof(f13,plain,(
% 1.22/0.53    ? [X0] : (? [X1] : (~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0))),
% 1.22/0.53    inference(flattening,[],[f12])).
% 1.22/0.53  fof(f12,plain,(
% 1.22/0.53    ? [X0] : (? [X1] : ((~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))) & ~v1_xboole_0(X0))),
% 1.22/0.53    inference(ennf_transformation,[],[f11])).
% 1.22/0.53  fof(f11,negated_conjecture,(
% 1.22/0.53    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (! [X2] : (m1_subset_1(X2,X0) => k3_funct_2(X0,X0,X1,X2) = X2) => r2_funct_2(X0,X0,X1,k6_partfun1(X0)))))),
% 1.22/0.53    inference(negated_conjecture,[],[f10])).
% 1.22/0.53  fof(f10,conjecture,(
% 1.22/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (! [X2] : (m1_subset_1(X2,X0) => k3_funct_2(X0,X0,X1,X2) = X2) => r2_funct_2(X0,X0,X1,k6_partfun1(X0)))))),
% 1.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t201_funct_2)).
% 1.22/0.53  fof(f162,plain,(
% 1.22/0.53    ~v1_funct_1(sK1)),
% 1.22/0.53    inference(subsumption_resolution,[],[f161,f38])).
% 1.22/0.53  fof(f38,plain,(
% 1.22/0.53    v1_funct_2(sK1,sK0,sK0)),
% 1.22/0.53    inference(cnf_transformation,[],[f29])).
% 1.22/0.53  fof(f161,plain,(
% 1.22/0.53    ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.22/0.53    inference(resolution,[],[f159,f39])).
% 1.22/0.53  fof(f39,plain,(
% 1.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.22/0.53    inference(cnf_transformation,[],[f29])).
% 1.22/0.53  fof(f159,plain,(
% 1.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X0,sK0,sK0) | ~v1_funct_1(X0)) )),
% 1.22/0.53    inference(subsumption_resolution,[],[f158,f37])).
% 1.22/0.53  fof(f158,plain,(
% 1.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X0,sK0,sK0) | ~v1_funct_1(X0) | ~v1_funct_1(sK1)) )),
% 1.22/0.53    inference(subsumption_resolution,[],[f157,f38])).
% 1.22/0.53  fof(f157,plain,(
% 1.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X0,sK0,sK0) | ~v1_funct_1(X0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) )),
% 1.22/0.53    inference(subsumption_resolution,[],[f156,f39])).
% 1.22/0.53  fof(f156,plain,(
% 1.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(X0,sK0,sK0) | ~v1_funct_1(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) )),
% 1.22/0.53    inference(resolution,[],[f147,f56])).
% 1.22/0.53  fof(f56,plain,(
% 1.22/0.53    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f26])).
% 1.22/0.53  fof(f26,plain,(
% 1.22/0.53    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.22/0.53    inference(flattening,[],[f25])).
% 1.22/0.53  fof(f25,plain,(
% 1.22/0.53    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.22/0.53    inference(ennf_transformation,[],[f9])).
% 1.22/0.53  fof(f9,axiom,(
% 1.22/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 1.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).
% 1.22/0.53  fof(f147,plain,(
% 1.22/0.53    ~r2_funct_2(sK0,sK0,sK1,sK1)),
% 1.22/0.53    inference(backward_demodulation,[],[f62,f146])).
% 1.22/0.53  fof(f146,plain,(
% 1.22/0.53    sK1 = k6_relat_1(sK0)),
% 1.22/0.53    inference(subsumption_resolution,[],[f145,f119])).
% 1.22/0.53  fof(f119,plain,(
% 1.22/0.53    m1_subset_1(sK2(sK0,sK1),sK0) | sK1 = k6_relat_1(sK0)),
% 1.22/0.53    inference(resolution,[],[f107,f45])).
% 1.22/0.53  fof(f45,plain,(
% 1.22/0.53    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f16])).
% 1.22/0.53  fof(f16,plain,(
% 1.22/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.22/0.53    inference(ennf_transformation,[],[f1])).
% 1.22/0.53  fof(f1,axiom,(
% 1.22/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.22/0.53  fof(f107,plain,(
% 1.22/0.53    r2_hidden(sK2(sK0,sK1),sK0) | sK1 = k6_relat_1(sK0)),
% 1.22/0.53    inference(forward_demodulation,[],[f106,f100])).
% 1.22/0.53  fof(f100,plain,(
% 1.22/0.53    sK0 = k1_relat_1(sK1)),
% 1.22/0.53    inference(subsumption_resolution,[],[f99,f90])).
% 1.22/0.53  fof(f90,plain,(
% 1.22/0.53    v1_relat_1(sK1)),
% 1.22/0.53    inference(resolution,[],[f39,f52])).
% 1.22/0.53  fof(f52,plain,(
% 1.22/0.53    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.22/0.53    inference(cnf_transformation,[],[f21])).
% 1.22/0.53  fof(f21,plain,(
% 1.22/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.22/0.53    inference(ennf_transformation,[],[f3])).
% 1.22/0.53  fof(f3,axiom,(
% 1.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.22/0.53  fof(f99,plain,(
% 1.22/0.53    sK0 = k1_relat_1(sK1) | ~v1_relat_1(sK1)),
% 1.22/0.53    inference(subsumption_resolution,[],[f98,f84])).
% 1.22/0.53  fof(f84,plain,(
% 1.22/0.53    v1_partfun1(sK1,sK0)),
% 1.22/0.53    inference(subsumption_resolution,[],[f83,f36])).
% 1.22/0.53  fof(f36,plain,(
% 1.22/0.53    ~v1_xboole_0(sK0)),
% 1.22/0.53    inference(cnf_transformation,[],[f29])).
% 1.22/0.53  fof(f83,plain,(
% 1.22/0.53    v1_partfun1(sK1,sK0) | v1_xboole_0(sK0)),
% 1.22/0.53    inference(subsumption_resolution,[],[f82,f39])).
% 1.22/0.53  fof(f82,plain,(
% 1.22/0.53    v1_partfun1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | v1_xboole_0(sK0)),
% 1.22/0.53    inference(subsumption_resolution,[],[f74,f37])).
% 1.22/0.53  fof(f74,plain,(
% 1.22/0.53    v1_partfun1(sK1,sK0) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | v1_xboole_0(sK0)),
% 1.22/0.53    inference(resolution,[],[f38,f44])).
% 1.22/0.53  fof(f44,plain,(
% 1.22/0.53    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f15])).
% 1.22/0.53  fof(f15,plain,(
% 1.22/0.53    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.22/0.53    inference(flattening,[],[f14])).
% 1.22/0.53  fof(f14,plain,(
% 1.22/0.53    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.22/0.53    inference(ennf_transformation,[],[f5])).
% 1.22/0.53  fof(f5,axiom,(
% 1.22/0.53    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.22/0.53  fof(f98,plain,(
% 1.22/0.53    sK0 = k1_relat_1(sK1) | ~v1_partfun1(sK1,sK0) | ~v1_relat_1(sK1)),
% 1.22/0.53    inference(resolution,[],[f89,f50])).
% 1.22/0.53  fof(f50,plain,(
% 1.22/0.53    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f35])).
% 1.22/0.53  fof(f35,plain,(
% 1.22/0.53    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.22/0.53    inference(nnf_transformation,[],[f20])).
% 1.22/0.53  fof(f20,plain,(
% 1.22/0.53    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.22/0.53    inference(flattening,[],[f19])).
% 1.22/0.53  fof(f19,plain,(
% 1.22/0.53    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.22/0.53    inference(ennf_transformation,[],[f6])).
% 1.22/0.53  fof(f6,axiom,(
% 1.22/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 1.22/0.53  fof(f89,plain,(
% 1.22/0.53    v4_relat_1(sK1,sK0)),
% 1.22/0.53    inference(resolution,[],[f39,f53])).
% 1.22/0.53  fof(f53,plain,(
% 1.22/0.53    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.22/0.53    inference(cnf_transformation,[],[f22])).
% 1.22/0.53  fof(f22,plain,(
% 1.22/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.22/0.53    inference(ennf_transformation,[],[f4])).
% 1.22/0.53  fof(f4,axiom,(
% 1.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.22/0.53  fof(f106,plain,(
% 1.22/0.53    sK1 = k6_relat_1(sK0) | r2_hidden(sK2(k1_relat_1(sK1),sK1),k1_relat_1(sK1))),
% 1.22/0.53    inference(subsumption_resolution,[],[f101,f90])).
% 1.22/0.53  fof(f101,plain,(
% 1.22/0.53    sK1 = k6_relat_1(sK0) | r2_hidden(sK2(k1_relat_1(sK1),sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 1.22/0.53    inference(backward_demodulation,[],[f68,f100])).
% 1.22/0.53  fof(f68,plain,(
% 1.22/0.53    sK1 = k6_relat_1(k1_relat_1(sK1)) | r2_hidden(sK2(k1_relat_1(sK1),sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 1.22/0.53    inference(resolution,[],[f37,f58])).
% 1.22/0.53  fof(f58,plain,(
% 1.22/0.53    ( ! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | r2_hidden(sK2(k1_relat_1(X1),X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.22/0.53    inference(equality_resolution,[],[f48])).
% 1.22/0.53  fof(f48,plain,(
% 1.22/0.53    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f34])).
% 1.22/0.53  fof(f34,plain,(
% 1.22/0.53    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).
% 1.22/0.53  fof(f33,plain,(
% 1.22/0.53    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 1.22/0.53    introduced(choice_axiom,[])).
% 1.22/0.53  fof(f32,plain,(
% 1.22/0.53    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.22/0.53    inference(rectify,[],[f31])).
% 1.22/0.53  fof(f31,plain,(
% 1.22/0.53    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.22/0.53    inference(flattening,[],[f30])).
% 1.22/0.53  fof(f30,plain,(
% 1.22/0.53    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.22/0.53    inference(nnf_transformation,[],[f18])).
% 1.22/0.53  fof(f18,plain,(
% 1.22/0.53    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.22/0.53    inference(flattening,[],[f17])).
% 1.22/0.53  fof(f17,plain,(
% 1.22/0.53    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.22/0.53    inference(ennf_transformation,[],[f2])).
% 1.22/0.53  fof(f2,axiom,(
% 1.22/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 1.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).
% 1.22/0.53  fof(f145,plain,(
% 1.22/0.53    sK1 = k6_relat_1(sK0) | ~m1_subset_1(sK2(sK0,sK1),sK0)),
% 1.22/0.53    inference(subsumption_resolution,[],[f144,f109])).
% 1.22/0.53  fof(f109,plain,(
% 1.22/0.53    sK2(sK0,sK1) != k1_funct_1(sK1,sK2(sK0,sK1)) | sK1 = k6_relat_1(sK0)),
% 1.22/0.53    inference(forward_demodulation,[],[f108,f100])).
% 1.22/0.53  fof(f108,plain,(
% 1.22/0.53    sK1 = k6_relat_1(sK0) | sK2(k1_relat_1(sK1),sK1) != k1_funct_1(sK1,sK2(k1_relat_1(sK1),sK1))),
% 1.22/0.53    inference(subsumption_resolution,[],[f102,f90])).
% 1.22/0.53  fof(f102,plain,(
% 1.22/0.53    sK1 = k6_relat_1(sK0) | sK2(k1_relat_1(sK1),sK1) != k1_funct_1(sK1,sK2(k1_relat_1(sK1),sK1)) | ~v1_relat_1(sK1)),
% 1.22/0.53    inference(backward_demodulation,[],[f69,f100])).
% 1.22/0.53  fof(f69,plain,(
% 1.22/0.53    sK1 = k6_relat_1(k1_relat_1(sK1)) | sK2(k1_relat_1(sK1),sK1) != k1_funct_1(sK1,sK2(k1_relat_1(sK1),sK1)) | ~v1_relat_1(sK1)),
% 1.22/0.53    inference(resolution,[],[f37,f57])).
% 1.22/0.53  fof(f57,plain,(
% 1.22/0.53    ( ! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | sK2(k1_relat_1(X1),X1) != k1_funct_1(X1,sK2(k1_relat_1(X1),X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.22/0.53    inference(equality_resolution,[],[f49])).
% 1.22/0.53  fof(f49,plain,(
% 1.22/0.53    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f34])).
% 1.22/0.53  fof(f144,plain,(
% 1.22/0.53    sK2(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | sK1 = k6_relat_1(sK0) | ~m1_subset_1(sK2(sK0,sK1),sK0)),
% 1.22/0.53    inference(subsumption_resolution,[],[f143,f36])).
% 1.22/0.53  fof(f143,plain,(
% 1.22/0.53    sK2(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | sK1 = k6_relat_1(sK0) | ~m1_subset_1(sK2(sK0,sK1),sK0) | v1_xboole_0(sK0)),
% 1.22/0.53    inference(subsumption_resolution,[],[f142,f37])).
% 1.22/0.53  fof(f142,plain,(
% 1.22/0.53    sK2(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | sK1 = k6_relat_1(sK0) | ~m1_subset_1(sK2(sK0,sK1),sK0) | ~v1_funct_1(sK1) | v1_xboole_0(sK0)),
% 1.22/0.53    inference(subsumption_resolution,[],[f141,f38])).
% 1.22/0.53  fof(f141,plain,(
% 1.22/0.53    sK2(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | sK1 = k6_relat_1(sK0) | ~m1_subset_1(sK2(sK0,sK1),sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v1_xboole_0(sK0)),
% 1.22/0.53    inference(subsumption_resolution,[],[f139,f39])).
% 1.22/0.53  fof(f139,plain,(
% 1.22/0.53    sK2(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | sK1 = k6_relat_1(sK0) | ~m1_subset_1(sK2(sK0,sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v1_xboole_0(sK0)),
% 1.22/0.53    inference(superposition,[],[f127,f55])).
% 1.22/0.53  fof(f55,plain,(
% 1.22/0.53    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f24])).
% 1.22/0.53  fof(f24,plain,(
% 1.22/0.53    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.22/0.53    inference(flattening,[],[f23])).
% 1.22/0.53  fof(f23,plain,(
% 1.22/0.53    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.22/0.53    inference(ennf_transformation,[],[f7])).
% 1.22/0.53  fof(f7,axiom,(
% 1.22/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 1.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 1.22/0.53  fof(f127,plain,(
% 1.22/0.53    sK2(sK0,sK1) = k3_funct_2(sK0,sK0,sK1,sK2(sK0,sK1)) | sK1 = k6_relat_1(sK0)),
% 1.22/0.53    inference(resolution,[],[f40,f119])).
% 1.22/0.53  fof(f40,plain,(
% 1.22/0.53    ( ! [X2] : (~m1_subset_1(X2,sK0) | k3_funct_2(sK0,sK0,sK1,X2) = X2) )),
% 1.22/0.53    inference(cnf_transformation,[],[f29])).
% 1.22/0.53  fof(f62,plain,(
% 1.22/0.53    ~r2_funct_2(sK0,sK0,sK1,k6_relat_1(sK0))),
% 1.22/0.53    inference(forward_demodulation,[],[f41,f42])).
% 1.22/0.53  fof(f42,plain,(
% 1.22/0.53    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f8])).
% 1.22/0.53  fof(f8,axiom,(
% 1.22/0.53    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.22/0.53  fof(f41,plain,(
% 1.22/0.53    ~r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))),
% 1.22/0.53    inference(cnf_transformation,[],[f29])).
% 1.22/0.53  % SZS output end Proof for theBenchmark
% 1.22/0.53  % (2478)------------------------------
% 1.22/0.53  % (2478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (2478)Termination reason: Refutation
% 1.22/0.53  
% 1.22/0.53  % (2478)Memory used [KB]: 1791
% 1.22/0.53  % (2478)Time elapsed: 0.067 s
% 1.22/0.53  % (2478)------------------------------
% 1.22/0.53  % (2478)------------------------------
% 1.22/0.53  % (2454)Success in time 0.163 s
%------------------------------------------------------------------------------
