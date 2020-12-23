%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 962 expanded)
%              Number of leaves         :   14 ( 300 expanded)
%              Depth                    :   27
%              Number of atoms          :  547 (14656 expanded)
%              Number of equality atoms :  216 (6301 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f217,plain,(
    $false ),
    inference(subsumption_resolution,[],[f216,f111])).

fof(f111,plain,(
    sK2 = k1_relat_1(sK4) ),
    inference(backward_demodulation,[],[f96,f110])).

fof(f110,plain,(
    sK2 = k1_relset_1(sK2,sK1,sK4) ),
    inference(subsumption_resolution,[],[f109,f49])).

fof(f49,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k2_funct_1(sK3) != sK4
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & ! [X4,X5] :
        ( ( ( k1_funct_1(sK4,X4) = X5
            & r2_hidden(X4,sK2) )
          | k1_funct_1(sK3,X5) != X4
          | ~ r2_hidden(X5,sK1) )
        & ( ( k1_funct_1(sK3,X5) = X4
            & r2_hidden(X5,sK1) )
          | k1_funct_1(sK4,X4) != X5
          | ~ r2_hidden(X4,sK2) ) )
    & v2_funct_1(sK3)
    & sK2 = k2_relset_1(sK1,sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f13,f30,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & ! [X4,X5] :
                ( ( ( k1_funct_1(X3,X4) = X5
                    & r2_hidden(X4,X1) )
                  | k1_funct_1(X2,X5) != X4
                  | ~ r2_hidden(X5,X0) )
                & ( ( k1_funct_1(X2,X5) = X4
                    & r2_hidden(X5,X0) )
                  | k1_funct_1(X3,X4) != X5
                  | ~ r2_hidden(X4,X1) ) )
            & v2_funct_1(X2)
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK3) != X3
          & k1_xboole_0 != sK2
          & k1_xboole_0 != sK1
          & ! [X5,X4] :
              ( ( ( k1_funct_1(X3,X4) = X5
                  & r2_hidden(X4,sK2) )
                | k1_funct_1(sK3,X5) != X4
                | ~ r2_hidden(X5,sK1) )
              & ( ( k1_funct_1(sK3,X5) = X4
                  & r2_hidden(X5,sK1) )
                | k1_funct_1(X3,X4) != X5
                | ~ r2_hidden(X4,sK2) ) )
          & v2_funct_1(sK3)
          & sK2 = k2_relset_1(sK1,sK2,sK3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
          & v1_funct_2(X3,sK2,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X3] :
        ( k2_funct_1(sK3) != X3
        & k1_xboole_0 != sK2
        & k1_xboole_0 != sK1
        & ! [X5,X4] :
            ( ( ( k1_funct_1(X3,X4) = X5
                & r2_hidden(X4,sK2) )
              | k1_funct_1(sK3,X5) != X4
              | ~ r2_hidden(X5,sK1) )
            & ( ( k1_funct_1(sK3,X5) = X4
                & r2_hidden(X5,sK1) )
              | k1_funct_1(X3,X4) != X5
              | ~ r2_hidden(X4,sK2) ) )
        & v2_funct_1(sK3)
        & sK2 = k2_relset_1(sK1,sK2,sK3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        & v1_funct_2(X3,sK2,sK1)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK3) != sK4
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & ! [X5,X4] :
          ( ( ( k1_funct_1(sK4,X4) = X5
              & r2_hidden(X4,sK2) )
            | k1_funct_1(sK3,X5) != X4
            | ~ r2_hidden(X5,sK1) )
          & ( ( k1_funct_1(sK3,X5) = X4
              & r2_hidden(X5,sK1) )
            | k1_funct_1(sK4,X4) != X5
            | ~ r2_hidden(X4,sK2) ) )
      & v2_funct_1(sK3)
      & sK2 = k2_relset_1(sK1,sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      & v1_funct_2(sK4,sK2,sK1)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & ! [X4,X5] :
              ( ( ( k1_funct_1(X3,X4) = X5
                  & r2_hidden(X4,X1) )
                | k1_funct_1(X2,X5) != X4
                | ~ r2_hidden(X5,X0) )
              & ( ( k1_funct_1(X2,X5) = X4
                  & r2_hidden(X5,X0) )
                | k1_funct_1(X3,X4) != X5
                | ~ r2_hidden(X4,X1) ) )
          & v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & ! [X4,X5] :
              ( ( ( k1_funct_1(X3,X4) = X5
                  & r2_hidden(X4,X1) )
                | k1_funct_1(X2,X5) != X4
                | ~ r2_hidden(X5,X0) )
              & ( ( k1_funct_1(X2,X5) = X4
                  & r2_hidden(X5,X0) )
                | k1_funct_1(X3,X4) != X5
                | ~ r2_hidden(X4,X1) ) )
          & v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X2,X5) = X4
                        & r2_hidden(X5,X0) )
                     => ( k1_funct_1(X3,X4) = X5
                        & r2_hidden(X4,X1) ) )
                    & ( ( k1_funct_1(X3,X4) = X5
                        & r2_hidden(X4,X1) )
                     => ( k1_funct_1(X2,X5) = X4
                        & r2_hidden(X5,X0) ) ) )
                & v2_funct_1(X2)
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( ! [X4,X5] :
                  ( ( ( k1_funct_1(X2,X5) = X4
                      & r2_hidden(X5,X0) )
                   => ( k1_funct_1(X3,X4) = X5
                      & r2_hidden(X4,X1) ) )
                  & ( ( k1_funct_1(X3,X4) = X5
                      & r2_hidden(X4,X1) )
                   => ( k1_funct_1(X2,X5) = X4
                      & r2_hidden(X5,X0) ) ) )
              & v2_funct_1(X2)
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_2)).

fof(f109,plain,
    ( k1_xboole_0 = sK1
    | sK2 = k1_relset_1(sK2,sK1,sK4) ),
    inference(subsumption_resolution,[],[f104,f41])).

fof(f41,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f104,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | k1_xboole_0 = sK1
    | sK2 = k1_relset_1(sK2,sK1,sK4) ),
    inference(resolution,[],[f60,f88])).

fof(f88,plain,(
    sP0(sK2,sK4,sK1) ),
    inference(resolution,[],[f64,f42])).

fof(f42,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f22,f27])).

fof(f27,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f96,plain,(
    k1_relset_1(sK2,sK1,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f58,f42])).

fof(f58,plain,(
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

fof(f216,plain,(
    sK2 != k1_relat_1(sK4) ),
    inference(forward_demodulation,[],[f215,f100])).

fof(f100,plain,(
    sK2 = k1_relat_1(k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f91,f99])).

fof(f99,plain,(
    sK2 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f97,f43])).

fof(f43,plain,(
    sK2 = k2_relset_1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f97,plain,(
    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f59,f39])).

fof(f39,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f91,plain,(
    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f90,f81])).

fof(f81,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f80,f39])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f52,f57])).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f90,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f89,f37])).

fof(f37,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f89,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f53,f44])).

fof(f44,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f215,plain,(
    k1_relat_1(sK4) != k1_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f214,f82])).

fof(f82,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f80,f42])).

fof(f214,plain,
    ( k1_relat_1(sK4) != k1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f213,f40])).

fof(f40,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f213,plain,
    ( k1_relat_1(sK4) != k1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f212,f167])).

fof(f167,plain,(
    v1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f163,f80])).

fof(f163,plain,(
    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subsumption_resolution,[],[f162,f38])).

fof(f38,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f162,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK3,sK1,sK2) ),
    inference(subsumption_resolution,[],[f161,f43])).

fof(f161,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK2 != k2_relset_1(sK1,sK2,sK3)
    | ~ v1_funct_2(sK3,sK1,sK2) ),
    inference(resolution,[],[f160,f39])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,sK3) != X1
      | ~ v1_funct_2(sK3,X0,X1) ) ),
    inference(subsumption_resolution,[],[f159,f37])).

fof(f159,plain,(
    ! [X0,X1] :
      ( k2_relset_1(X0,X1,sK3) != X1
      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK3,X0,X1)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f69,f44])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f212,plain,
    ( k1_relat_1(sK4) != k1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f211,f141])).

fof(f141,plain,(
    v1_funct_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f140,f38])).

fof(f140,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK2) ),
    inference(subsumption_resolution,[],[f139,f43])).

fof(f139,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | sK2 != k2_relset_1(sK1,sK2,sK3)
    | ~ v1_funct_2(sK3,sK1,sK2) ),
    inference(resolution,[],[f138,f39])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_funct_1(sK3))
      | k2_relset_1(X0,X1,sK3) != X1
      | ~ v1_funct_2(sK3,X0,X1) ) ),
    inference(subsumption_resolution,[],[f137,f37])).

fof(f137,plain,(
    ! [X0,X1] :
      ( k2_relset_1(X0,X1,sK3) != X1
      | v1_funct_1(k2_funct_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK3,X0,X1)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f67,f44])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_1(k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f211,plain,
    ( k1_relat_1(sK4) != k1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f210,f51])).

fof(f51,plain,(
    k2_funct_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f31])).

fof(f210,plain,
    ( k2_funct_1(sK3) = sK4
    | k1_relat_1(sK4) != k1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(trivial_inequality_removal,[],[f209])).

fof(f209,plain,
    ( k1_funct_1(sK4,sK5(sK4,k2_funct_1(sK3))) != k1_funct_1(sK4,sK5(sK4,k2_funct_1(sK3)))
    | k2_funct_1(sK3) = sK4
    | k1_relat_1(sK4) != k1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(superposition,[],[f56,f207])).

fof(f207,plain,(
    k1_funct_1(sK4,sK5(sK4,k2_funct_1(sK3))) = k1_funct_1(k2_funct_1(sK3),sK5(sK4,k2_funct_1(sK3))) ),
    inference(forward_demodulation,[],[f205,f179])).

fof(f179,plain,(
    sK5(sK4,k2_funct_1(sK3)) = k1_funct_1(sK3,k1_funct_1(sK4,sK5(sK4,k2_funct_1(sK3)))) ),
    inference(resolution,[],[f172,f73])).

fof(f73,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK2)
      | k1_funct_1(sK3,k1_funct_1(sK4,X4)) = X4 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X4,X5] :
      ( k1_funct_1(sK3,X5) = X4
      | k1_funct_1(sK4,X4) != X5
      | ~ r2_hidden(X4,sK2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f172,plain,(
    r2_hidden(sK5(sK4,k2_funct_1(sK3)),sK2) ),
    inference(subsumption_resolution,[],[f146,f167])).

fof(f146,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | r2_hidden(sK5(sK4,k2_funct_1(sK3)),sK2) ),
    inference(subsumption_resolution,[],[f145,f51])).

fof(f145,plain,
    ( r2_hidden(sK5(sK4,k2_funct_1(sK3)),sK2)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | k2_funct_1(sK3) = sK4 ),
    inference(subsumption_resolution,[],[f142,f100])).

fof(f142,plain,
    ( r2_hidden(sK5(sK4,k2_funct_1(sK3)),sK2)
    | sK2 != k1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | k2_funct_1(sK3) = sK4 ),
    inference(resolution,[],[f141,f125])).

fof(f125,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | r2_hidden(sK5(sK4,X1),sK2)
      | k1_relat_1(X1) != sK2
      | ~ v1_relat_1(X1)
      | sK4 = X1 ) ),
    inference(forward_demodulation,[],[f124,f111])).

fof(f124,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK4,X1),sK2)
      | k1_relat_1(X1) != k1_relat_1(sK4)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | sK4 = X1 ) ),
    inference(forward_demodulation,[],[f123,f111])).

fof(f123,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK4,X1),k1_relat_1(sK4))
      | k1_relat_1(X1) != k1_relat_1(sK4)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | sK4 = X1 ) ),
    inference(subsumption_resolution,[],[f119,f82])).

fof(f119,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK4,X1),k1_relat_1(sK4))
      | k1_relat_1(X1) != k1_relat_1(sK4)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | sK4 = X1
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f55,f40])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | X0 = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
            & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f205,plain,(
    k1_funct_1(sK4,sK5(sK4,k2_funct_1(sK3))) = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,k1_funct_1(sK4,sK5(sK4,k2_funct_1(sK3))))) ),
    inference(resolution,[],[f203,f172])).

fof(f203,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | k1_funct_1(sK4,X0) = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,k1_funct_1(sK4,X0))) ) ),
    inference(resolution,[],[f202,f74])).

fof(f74,plain,(
    ! [X4] :
      ( r2_hidden(k1_funct_1(sK4,X4),sK1)
      | ~ r2_hidden(X4,sK2) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X5] :
      ( r2_hidden(X5,sK1)
      | k1_funct_1(sK4,X4) != X5
      | ~ r2_hidden(X4,sK2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f202,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f201,f38])).

fof(f201,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
      | ~ v1_funct_2(sK3,sK1,sK2) ) ),
    inference(subsumption_resolution,[],[f200,f50])).

fof(f50,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f200,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
      | k1_xboole_0 = sK2
      | ~ v1_funct_2(sK3,sK1,sK2) ) ),
    inference(resolution,[],[f199,f39])).

fof(f199,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ r2_hidden(X1,X2)
      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X1)) = X1
      | k1_xboole_0 = X0
      | ~ v1_funct_2(sK3,X2,X0) ) ),
    inference(subsumption_resolution,[],[f198,f37])).

fof(f198,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X1,X2)
      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X1)) = X1
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_2(sK3,X2,X0)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f70,f44])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:19:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (24610)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (24628)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (24627)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (24623)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.52  % (24619)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (24620)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (24611)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  % (24615)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (24609)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.53  % (24618)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.53  % (24606)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.53  % (24625)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.53  % (24610)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f217,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f216,f111])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    sK2 = k1_relat_1(sK4)),
% 0.22/0.53    inference(backward_demodulation,[],[f96,f110])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    sK2 = k1_relset_1(sK2,sK1,sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f109,f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    k1_xboole_0 != sK1),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    (k2_funct_1(sK3) != sK4 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & ! [X4,X5] : (((k1_funct_1(sK4,X4) = X5 & r2_hidden(X4,sK2)) | k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK1)) & ((k1_funct_1(sK3,X5) = X4 & r2_hidden(X5,sK1)) | k1_funct_1(sK4,X4) != X5 | ~r2_hidden(X4,sK2))) & v2_funct_1(sK3) & sK2 = k2_relset_1(sK1,sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f13,f30,f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X4,X5] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) | k1_funct_1(X2,X5) != X4 | ~r2_hidden(X5,X0)) & ((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) | k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,X1))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK3) != X3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & ! [X5,X4] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,sK2)) | k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK1)) & ((k1_funct_1(sK3,X5) = X4 & r2_hidden(X5,sK1)) | k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,sK2))) & v2_funct_1(sK3) & sK2 = k2_relset_1(sK1,sK2,sK3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ? [X3] : (k2_funct_1(sK3) != X3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & ! [X5,X4] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,sK2)) | k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK1)) & ((k1_funct_1(sK3,X5) = X4 & r2_hidden(X5,sK1)) | k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,sK2))) & v2_funct_1(sK3) & sK2 = k2_relset_1(sK1,sK2,sK3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) => (k2_funct_1(sK3) != sK4 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & ! [X5,X4] : (((k1_funct_1(sK4,X4) = X5 & r2_hidden(X4,sK2)) | k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK1)) & ((k1_funct_1(sK3,X5) = X4 & r2_hidden(X5,sK1)) | k1_funct_1(sK4,X4) != X5 | ~r2_hidden(X4,sK2))) & v2_funct_1(sK3) & sK2 = k2_relset_1(sK1,sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X4,X5] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) | k1_funct_1(X2,X5) != X4 | ~r2_hidden(X5,X0)) & ((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) | k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,X1))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.53    inference(flattening,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (! [X4,X5] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) | (k1_funct_1(X2,X5) != X4 | ~r2_hidden(X5,X0))) & ((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) | (k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,X1)))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((! [X4,X5] : (((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) => (k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1))) & ((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) => (k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.22/0.53    inference(negated_conjecture,[],[f10])).
% 0.22/0.53  fof(f10,conjecture,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((! [X4,X5] : (((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) => (k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1))) & ((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) => (k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_2)).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | sK2 = k1_relset_1(sK2,sK1,sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f104,f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    v1_funct_2(sK4,sK2,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    ~v1_funct_2(sK4,sK2,sK1) | k1_xboole_0 = sK1 | sK2 = k1_relset_1(sK2,sK1,sK4)),
% 0.22/0.53    inference(resolution,[],[f60,f88])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    sP0(sK2,sK4,sK1)),
% 0.22/0.53    inference(resolution,[],[f64,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(nnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(definition_folding,[],[f22,f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(flattening,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 0.22/0.53    inference(rectify,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f27])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    k1_relset_1(sK2,sK1,sK4) = k1_relat_1(sK4)),
% 0.22/0.53    inference(resolution,[],[f58,f42])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.53  fof(f216,plain,(
% 0.22/0.53    sK2 != k1_relat_1(sK4)),
% 0.22/0.53    inference(forward_demodulation,[],[f215,f100])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    sK2 = k1_relat_1(k2_funct_1(sK3))),
% 0.22/0.53    inference(backward_demodulation,[],[f91,f99])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    sK2 = k2_relat_1(sK3)),
% 0.22/0.53    inference(forward_demodulation,[],[f97,f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    sK2 = k2_relset_1(sK1,sK2,sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 0.22/0.53    inference(resolution,[],[f59,f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 0.22/0.53    inference(subsumption_resolution,[],[f90,f81])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    v1_relat_1(sK3)),
% 0.22/0.53    inference(resolution,[],[f80,f39])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 0.22/0.53    inference(resolution,[],[f52,f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f89,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    v1_funct_1(sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.22/0.53    inference(resolution,[],[f53,f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    v2_funct_1(sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.53  fof(f215,plain,(
% 0.22/0.53    k1_relat_1(sK4) != k1_relat_1(k2_funct_1(sK3))),
% 0.22/0.53    inference(subsumption_resolution,[],[f214,f82])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    v1_relat_1(sK4)),
% 0.22/0.53    inference(resolution,[],[f80,f42])).
% 0.22/0.53  fof(f214,plain,(
% 0.22/0.53    k1_relat_1(sK4) != k1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f213,f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    v1_funct_1(sK4)),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f213,plain,(
% 0.22/0.53    k1_relat_1(sK4) != k1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f212,f167])).
% 0.22/0.53  fof(f167,plain,(
% 0.22/0.53    v1_relat_1(k2_funct_1(sK3))),
% 0.22/0.53    inference(resolution,[],[f163,f80])).
% 0.22/0.53  fof(f163,plain,(
% 0.22/0.53    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.22/0.53    inference(subsumption_resolution,[],[f162,f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    v1_funct_2(sK3,sK1,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f162,plain,(
% 0.22/0.53    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK3,sK1,sK2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f161,f43])).
% 0.22/0.53  fof(f161,plain,(
% 0.22/0.53    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK2 != k2_relset_1(sK1,sK2,sK3) | ~v1_funct_2(sK3,sK1,sK2)),
% 0.22/0.53    inference(resolution,[],[f160,f39])).
% 0.22/0.53  fof(f160,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,sK3) != X1 | ~v1_funct_2(sK3,X0,X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f159,f37])).
% 0.22/0.53  fof(f159,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK3) != X1 | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1) | ~v1_funct_1(sK3)) )),
% 0.22/0.53    inference(resolution,[],[f69,f44])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.53    inference(flattening,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.53  fof(f212,plain,(
% 0.22/0.53    k1_relat_1(sK4) != k1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f211,f141])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    v1_funct_1(k2_funct_1(sK3))),
% 0.22/0.53    inference(subsumption_resolution,[],[f140,f38])).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    v1_funct_1(k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f139,f43])).
% 0.22/0.53  fof(f139,plain,(
% 0.22/0.53    v1_funct_1(k2_funct_1(sK3)) | sK2 != k2_relset_1(sK1,sK2,sK3) | ~v1_funct_2(sK3,sK1,sK2)),
% 0.22/0.53    inference(resolution,[],[f138,f39])).
% 0.22/0.53  fof(f138,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_funct_1(sK3)) | k2_relset_1(X0,X1,sK3) != X1 | ~v1_funct_2(sK3,X0,X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f137,f37])).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK3) != X1 | v1_funct_1(k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1) | ~v1_funct_1(sK3)) )),
% 0.22/0.53    inference(resolution,[],[f67,f44])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_1(k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f211,plain,(
% 0.22/0.53    k1_relat_1(sK4) != k1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f210,f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    k2_funct_1(sK3) != sK4),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f210,plain,(
% 0.22/0.53    k2_funct_1(sK3) = sK4 | k1_relat_1(sK4) != k1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f209])).
% 0.22/0.53  fof(f209,plain,(
% 0.22/0.53    k1_funct_1(sK4,sK5(sK4,k2_funct_1(sK3))) != k1_funct_1(sK4,sK5(sK4,k2_funct_1(sK3))) | k2_funct_1(sK3) = sK4 | k1_relat_1(sK4) != k1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.22/0.53    inference(superposition,[],[f56,f207])).
% 0.22/0.53  fof(f207,plain,(
% 0.22/0.53    k1_funct_1(sK4,sK5(sK4,k2_funct_1(sK3))) = k1_funct_1(k2_funct_1(sK3),sK5(sK4,k2_funct_1(sK3)))),
% 0.22/0.53    inference(forward_demodulation,[],[f205,f179])).
% 0.22/0.53  fof(f179,plain,(
% 0.22/0.53    sK5(sK4,k2_funct_1(sK3)) = k1_funct_1(sK3,k1_funct_1(sK4,sK5(sK4,k2_funct_1(sK3))))),
% 0.22/0.53    inference(resolution,[],[f172,f73])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ( ! [X4] : (~r2_hidden(X4,sK2) | k1_funct_1(sK3,k1_funct_1(sK4,X4)) = X4) )),
% 0.22/0.53    inference(equality_resolution,[],[f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X4,X5] : (k1_funct_1(sK3,X5) = X4 | k1_funct_1(sK4,X4) != X5 | ~r2_hidden(X4,sK2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f172,plain,(
% 0.22/0.53    r2_hidden(sK5(sK4,k2_funct_1(sK3)),sK2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f146,f167])).
% 0.22/0.53  fof(f146,plain,(
% 0.22/0.53    ~v1_relat_1(k2_funct_1(sK3)) | r2_hidden(sK5(sK4,k2_funct_1(sK3)),sK2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f145,f51])).
% 0.22/0.53  fof(f145,plain,(
% 0.22/0.53    r2_hidden(sK5(sK4,k2_funct_1(sK3)),sK2) | ~v1_relat_1(k2_funct_1(sK3)) | k2_funct_1(sK3) = sK4),
% 0.22/0.53    inference(subsumption_resolution,[],[f142,f100])).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    r2_hidden(sK5(sK4,k2_funct_1(sK3)),sK2) | sK2 != k1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | k2_funct_1(sK3) = sK4),
% 0.22/0.53    inference(resolution,[],[f141,f125])).
% 0.22/0.53  fof(f125,plain,(
% 0.22/0.53    ( ! [X1] : (~v1_funct_1(X1) | r2_hidden(sK5(sK4,X1),sK2) | k1_relat_1(X1) != sK2 | ~v1_relat_1(X1) | sK4 = X1) )),
% 0.22/0.53    inference(forward_demodulation,[],[f124,f111])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    ( ! [X1] : (r2_hidden(sK5(sK4,X1),sK2) | k1_relat_1(X1) != k1_relat_1(sK4) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | sK4 = X1) )),
% 0.22/0.53    inference(forward_demodulation,[],[f123,f111])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    ( ! [X1] : (r2_hidden(sK5(sK4,X1),k1_relat_1(sK4)) | k1_relat_1(X1) != k1_relat_1(sK4) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | sK4 = X1) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f119,f82])).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    ( ! [X1] : (r2_hidden(sK5(sK4,X1),k1_relat_1(sK4)) | k1_relat_1(X1) != k1_relat_1(sK4) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | sK4 = X1 | ~v1_relat_1(sK4)) )),
% 0.22/0.53    inference(resolution,[],[f55,f40])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | X0 = X1 | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 0.22/0.53  fof(f205,plain,(
% 0.22/0.53    k1_funct_1(sK4,sK5(sK4,k2_funct_1(sK3))) = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,k1_funct_1(sK4,sK5(sK4,k2_funct_1(sK3)))))),
% 0.22/0.53    inference(resolution,[],[f203,f172])).
% 0.22/0.53  fof(f203,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,sK2) | k1_funct_1(sK4,X0) = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,k1_funct_1(sK4,X0)))) )),
% 0.22/0.53    inference(resolution,[],[f202,f74])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ( ! [X4] : (r2_hidden(k1_funct_1(sK4,X4),sK1) | ~r2_hidden(X4,sK2)) )),
% 0.22/0.53    inference(equality_resolution,[],[f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X4,X5] : (r2_hidden(X5,sK1) | k1_funct_1(sK4,X4) != X5 | ~r2_hidden(X4,sK2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f202,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f201,f38])).
% 0.22/0.53  fof(f201,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0 | ~v1_funct_2(sK3,sK1,sK2)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f200,f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    k1_xboole_0 != sK2),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f200,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0 | k1_xboole_0 = sK2 | ~v1_funct_2(sK3,sK1,sK2)) )),
% 0.22/0.53    inference(resolution,[],[f199,f39])).
% 0.22/0.53  fof(f199,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~r2_hidden(X1,X2) | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X1)) = X1 | k1_xboole_0 = X0 | ~v1_funct_2(sK3,X2,X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f198,f37])).
% 0.22/0.53  fof(f198,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r2_hidden(X1,X2) | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X1)) = X1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_2(sK3,X2,X0) | ~v1_funct_1(sK3)) )),
% 0.22/0.53    inference(resolution,[],[f70,f44])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~v2_funct_1(X3) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.53    inference(flattening,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) | X0 = X1 | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (24610)------------------------------
% 0.22/0.53  % (24610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (24610)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (24610)Memory used [KB]: 6396
% 0.22/0.53  % (24610)Time elapsed: 0.107 s
% 0.22/0.53  % (24610)------------------------------
% 0.22/0.53  % (24610)------------------------------
% 0.22/0.53  % (24599)Success in time 0.162 s
%------------------------------------------------------------------------------
