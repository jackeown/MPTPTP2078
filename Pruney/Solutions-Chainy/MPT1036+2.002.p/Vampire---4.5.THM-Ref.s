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
% DateTime   : Thu Dec  3 13:06:52 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :  118 (3703 expanded)
%              Number of leaves         :   11 (1068 expanded)
%              Depth                    :   68
%              Number of atoms          :  563 (30806 expanded)
%              Number of equality atoms :  128 (5702 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f157,plain,(
    $false ),
    inference(resolution,[],[f156,f146])).

fof(f146,plain,(
    ~ r1_partfun1(sK1,sK2) ),
    inference(trivial_inequality_removal,[],[f143])).

fof(f143,plain,
    ( k1_funct_1(sK1,sK3) != k1_funct_1(sK1,sK3)
    | ~ r1_partfun1(sK1,sK2) ),
    inference(backward_demodulation,[],[f38,f142])).

fof(f142,plain,(
    k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f140])).

fof(f140,plain,
    ( k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) ),
    inference(resolution,[],[f139,f120])).

fof(f120,plain,
    ( r1_partfun1(sK1,sK2)
    | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) ),
    inference(resolution,[],[f119,f49])).

fof(f49,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f45,f32])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ( k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
        & r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1)) )
      | ~ r1_partfun1(sK1,sK2) )
    & ( ! [X4] :
          ( k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4)
          | ~ r2_hidden(X4,k1_relset_1(sK0,sK0,sK1)) )
      | r1_partfun1(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
                  & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
              | ~ r1_partfun1(X1,X2) )
            & ( ! [X4] :
                  ( k1_funct_1(X1,X4) = k1_funct_1(X2,X4)
                  | ~ r2_hidden(X4,k1_relset_1(X0,X0,X1)) )
              | r1_partfun1(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X2,X3) != k1_funct_1(sK1,X3)
                & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1)) )
            | ~ r1_partfun1(sK1,X2) )
          & ( ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(sK1,X4)
                | ~ r2_hidden(X4,k1_relset_1(sK0,sK0,sK1)) )
            | r1_partfun1(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( k1_funct_1(X2,X3) != k1_funct_1(sK1,X3)
              & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1)) )
          | ~ r1_partfun1(sK1,X2) )
        & ( ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(sK1,X4)
              | ~ r2_hidden(X4,k1_relset_1(sK0,sK0,sK1)) )
          | r1_partfun1(sK1,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v1_funct_2(X2,sK0,sK0)
        & v1_funct_1(X2) )
   => ( ( ? [X3] :
            ( k1_funct_1(sK1,X3) != k1_funct_1(sK2,X3)
            & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1)) )
        | ~ r1_partfun1(sK1,sK2) )
      & ( ! [X4] :
            ( k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4)
            | ~ r2_hidden(X4,k1_relset_1(sK0,sK0,sK1)) )
        | r1_partfun1(sK1,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X3] :
        ( k1_funct_1(sK1,X3) != k1_funct_1(sK2,X3)
        & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1)) )
   => ( k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
      & r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
                & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
            | ~ r1_partfun1(X1,X2) )
          & ( ! [X4] :
                ( k1_funct_1(X1,X4) = k1_funct_1(X2,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X0,X1)) )
            | r1_partfun1(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
                & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
            | ~ r1_partfun1(X1,X2) )
          & ( ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                | ~ r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
            | r1_partfun1(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
                & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
            | ~ r1_partfun1(X1,X2) )
          & ( ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                | ~ r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
            | r1_partfun1(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_partfun1(X1,X2)
          <~> ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                | ~ r2_hidden(X3,k1_relset_1(X0,X0,X1)) ) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_partfun1(X1,X2)
          <~> ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                | ~ r2_hidden(X3,k1_relset_1(X0,X0,X1)) ) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r1_partfun1(X1,X2)
            <=> ! [X3] :
                  ( r2_hidden(X3,k1_relset_1(X0,X0,X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r1_partfun1(X1,X2)
          <=> ! [X3] :
                ( r2_hidden(X3,k1_relset_1(X0,X0,X1))
               => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_2)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f119,plain,
    ( ~ v1_relat_1(sK1)
    | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | r1_partfun1(sK1,sK2) ),
    inference(resolution,[],[f118,f50])).

fof(f50,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f45,f35])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f118,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | r1_partfun1(sK1,sK2) ),
    inference(resolution,[],[f117,f53])).

fof(f53,plain,(
    v4_relat_1(sK1,sK0) ),
    inference(resolution,[],[f47,f32])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f117,plain,
    ( ~ v4_relat_1(sK1,sK0)
    | r1_partfun1(sK1,sK2)
    | ~ v1_relat_1(sK1)
    | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | ~ v1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,
    ( ~ v1_relat_1(sK2)
    | r1_partfun1(sK1,sK2)
    | ~ v1_relat_1(sK1)
    | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | ~ v4_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f115,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f115,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK2)
    | r1_partfun1(sK1,sK2)
    | ~ v1_relat_1(sK1)
    | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) ),
    inference(resolution,[],[f113,f31])).

fof(f31,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f113,plain,
    ( ~ v1_funct_1(sK1)
    | ~ r1_tarski(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK2)
    | r1_partfun1(sK1,sK2)
    | ~ v1_relat_1(sK1)
    | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) ),
    inference(resolution,[],[f112,f33])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f112,plain,
    ( ~ v1_funct_1(sK2)
    | r1_partfun1(sK1,sK2)
    | ~ r1_tarski(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) ),
    inference(forward_demodulation,[],[f111,f66])).

fof(f66,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(resolution,[],[f64,f35])).

fof(f64,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k1_relat_1(sK2) ),
    inference(resolution,[],[f63,f33])).

fof(f63,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f62,f58])).

fof(f58,plain,(
    k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f46,f35])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f62,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f44,f34])).

fof(f34,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f111,plain,
    ( r1_partfun1(sK1,sK2)
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) ),
    inference(trivial_inequality_removal,[],[f110])).

fof(f110,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK1,sK4(sK1,sK2))
    | r1_partfun1(sK1,sK2)
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) ),
    inference(superposition,[],[f41,f109])).

fof(f109,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
    | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f108])).

fof(f108,plain,
    ( k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(resolution,[],[f106,f93])).

fof(f93,plain,
    ( r1_partfun1(sK1,sK2)
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(resolution,[],[f92,f49])).

fof(f92,plain,
    ( ~ v1_relat_1(sK1)
    | r1_partfun1(sK1,sK2)
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(resolution,[],[f91,f50])).

fof(f91,plain,
    ( ~ v1_relat_1(sK2)
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
    | r1_partfun1(sK1,sK2)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f90,f53])).

fof(f90,plain,
    ( ~ v4_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
    | r1_partfun1(sK1,sK2)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f88,f42])).

fof(f88,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),sK0)
    | r1_partfun1(sK1,sK2)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(resolution,[],[f77,f33])).

fof(f77,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | r1_partfun1(sK1,sK2)
    | ~ r1_tarski(k1_relat_1(sK1),sK0)
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK2)
    | r1_partfun1(sK1,sK2)
    | ~ v1_funct_1(sK2)
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
    | r1_partfun1(sK1,sK2) ),
    inference(superposition,[],[f74,f66])).

fof(f74,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | r1_partfun1(sK1,X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(sK1,sK4(sK1,X0)) = k1_funct_1(sK2,sK4(sK1,X0))
      | r1_partfun1(sK1,sK2) ) ),
    inference(resolution,[],[f73,f49])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r1_partfun1(sK1,X0)
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(X0))
      | k1_funct_1(sK1,sK4(sK1,X0)) = k1_funct_1(sK2,sK4(sK1,X0))
      | r1_partfun1(sK1,sK2) ) ),
    inference(resolution,[],[f65,f31])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK1)
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r1_partfun1(sK1,X0)
      | ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,sK4(sK1,X0)) = k1_funct_1(sK2,sK4(sK1,X0))
      | r1_partfun1(sK1,sK2) ) ),
    inference(resolution,[],[f40,f59])).

fof(f59,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_relat_1(sK1))
      | k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4)
      | r1_partfun1(sK1,sK2) ) ),
    inference(backward_demodulation,[],[f36,f57])).

fof(f57,plain,(
    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(resolution,[],[f46,f32])).

fof(f36,plain,(
    ! [X4] :
      ( k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4)
      | ~ r2_hidden(X4,k1_relset_1(sK0,sK0,sK1))
      | r1_partfun1(sK1,sK2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | r1_partfun1(X0,X1)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
                & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) )
            & ( ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(X0,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) ) )
            & ( ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(X0,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) ) )
            & ( ! [X2] :
                  ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                  | ~ r2_hidden(X2,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f106,plain,
    ( ~ r1_partfun1(sK1,sK2)
    | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(resolution,[],[f105,f60])).

fof(f60,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | ~ r1_partfun1(sK1,sK2) ),
    inference(backward_demodulation,[],[f37,f57])).

fof(f37,plain,
    ( r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1))
    | ~ r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f105,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
      | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0) ) ),
    inference(resolution,[],[f104,f49])).

fof(f104,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0) ) ),
    inference(resolution,[],[f103,f50])).

fof(f103,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
      | ~ v1_relat_1(sK1)
      | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0) ) ),
    inference(resolution,[],[f102,f53])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK1,sK0)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK2)
      | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
      | ~ v1_relat_1(sK1)
      | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0) ) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,(
    ! [X0] :
      ( k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK2)
      | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
      | ~ v1_relat_1(sK1)
      | ~ v4_relat_1(sK1,sK0)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f100,f42])).

% (23617)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% (23610)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% (23618)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% (23623)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% (23629)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% (23608)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% (23619)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
fof(f100,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK1),sK0)
      | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK2)
      | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f99,f31])).

fof(f99,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0)
      | ~ r1_tarski(k1_relat_1(sK1),sK0)
      | ~ v1_relat_1(sK2)
      | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f96,f33])).

fof(f96,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK2)
      | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0)
      | ~ r1_tarski(k1_relat_1(sK1),sK0)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(forward_demodulation,[],[f95,f66])).

fof(f95,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0)
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f93,f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_partfun1(X0,X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X1,X3) = k1_funct_1(X0,X3)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | r1_partfun1(X0,X1)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f139,plain,
    ( ~ r1_partfun1(sK1,sK2)
    | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f137])).

fof(f137,plain,
    ( k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | ~ r1_partfun1(sK1,sK2) ),
    inference(resolution,[],[f136,f60])).

fof(f136,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
      | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0) ) ),
    inference(resolution,[],[f135,f49])).

fof(f135,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0) ) ),
    inference(resolution,[],[f131,f50])).

fof(f131,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
      | ~ v1_relat_1(sK1)
      | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0) ) ),
    inference(resolution,[],[f130,f53])).

fof(f130,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK1,sK0)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK2)
      | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
      | ~ v1_relat_1(sK1)
      | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0) ) ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,(
    ! [X0] :
      ( k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK2)
      | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
      | ~ v1_relat_1(sK1)
      | ~ v4_relat_1(sK1,sK0)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f128,f42])).

fof(f128,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK1),sK0)
      | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK2)
      | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f127,f31])).

fof(f127,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0)
      | ~ r1_tarski(k1_relat_1(sK1),sK0)
      | ~ v1_relat_1(sK2)
      | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f126,f33])).

fof(f126,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK2)
      | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0)
      | ~ r1_tarski(k1_relat_1(sK1),sK0)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(forward_demodulation,[],[f124,f66])).

fof(f124,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0)
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f120,f39])).

fof(f38,plain,
    ( ~ r1_partfun1(sK1,sK2)
    | k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f156,plain,(
    r1_partfun1(sK1,sK2) ),
    inference(resolution,[],[f155,f49])).

fof(f155,plain,
    ( ~ v1_relat_1(sK1)
    | r1_partfun1(sK1,sK2) ),
    inference(resolution,[],[f154,f50])).

fof(f154,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | r1_partfun1(sK1,sK2) ),
    inference(resolution,[],[f153,f53])).

fof(f153,plain,
    ( ~ v4_relat_1(sK1,sK0)
    | r1_partfun1(sK1,sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,
    ( ~ v1_relat_1(sK2)
    | r1_partfun1(sK1,sK2)
    | ~ v1_relat_1(sK1)
    | ~ v4_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f151,f42])).

fof(f151,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK2)
    | r1_partfun1(sK1,sK2)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f150,f31])).

fof(f150,plain,
    ( ~ v1_funct_1(sK1)
    | ~ r1_tarski(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK2)
    | r1_partfun1(sK1,sK2)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f149,f33])).

fof(f149,plain,
    ( ~ v1_funct_1(sK2)
    | r1_partfun1(sK1,sK2)
    | ~ r1_tarski(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(forward_demodulation,[],[f148,f66])).

fof(f148,plain,
    ( r1_partfun1(sK1,sK2)
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(trivial_inequality_removal,[],[f147])).

fof(f147,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK1,sK4(sK1,sK2))
    | r1_partfun1(sK1,sK2)
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f41,f145])).

fof(f145,plain,(
    k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(trivial_inequality_removal,[],[f144])).

fof(f144,plain,
    ( k1_funct_1(sK1,sK3) != k1_funct_1(sK1,sK3)
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(backward_demodulation,[],[f94,f142])).

fof(f94,plain,
    ( k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(resolution,[],[f93,f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:44:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (23609)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.44  % (23609)Refutation not found, incomplete strategy% (23609)------------------------------
% 0.20/0.44  % (23609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (23609)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.44  
% 0.20/0.44  % (23609)Memory used [KB]: 10618
% 0.20/0.44  % (23609)Time elapsed: 0.043 s
% 0.20/0.44  % (23609)------------------------------
% 0.20/0.44  % (23609)------------------------------
% 0.20/0.47  % (23624)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.48  % (23607)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.52  % (23606)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.52  % (23616)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.52  % (23611)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.53  % (23622)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.54  % (23615)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.54  % (23622)Refutation not found, incomplete strategy% (23622)------------------------------
% 0.20/0.54  % (23622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (23626)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.54  % (23616)Refutation not found, incomplete strategy% (23616)------------------------------
% 0.20/0.54  % (23616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (23616)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (23616)Memory used [KB]: 10618
% 0.20/0.54  % (23616)Time elapsed: 0.113 s
% 0.20/0.54  % (23616)------------------------------
% 0.20/0.54  % (23616)------------------------------
% 0.20/0.54  % (23622)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (23622)Memory used [KB]: 1663
% 0.20/0.54  % (23622)Time elapsed: 0.072 s
% 0.20/0.54  % (23622)------------------------------
% 0.20/0.54  % (23622)------------------------------
% 1.44/0.54  % (23614)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.44/0.54  % (23615)Refutation found. Thanks to Tanya!
% 1.44/0.54  % SZS status Theorem for theBenchmark
% 1.44/0.54  % SZS output start Proof for theBenchmark
% 1.44/0.54  fof(f157,plain,(
% 1.44/0.54    $false),
% 1.44/0.54    inference(resolution,[],[f156,f146])).
% 1.44/0.54  fof(f146,plain,(
% 1.44/0.54    ~r1_partfun1(sK1,sK2)),
% 1.44/0.54    inference(trivial_inequality_removal,[],[f143])).
% 1.44/0.54  fof(f143,plain,(
% 1.44/0.54    k1_funct_1(sK1,sK3) != k1_funct_1(sK1,sK3) | ~r1_partfun1(sK1,sK2)),
% 1.44/0.54    inference(backward_demodulation,[],[f38,f142])).
% 1.44/0.54  fof(f142,plain,(
% 1.44/0.54    k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)),
% 1.44/0.54    inference(duplicate_literal_removal,[],[f140])).
% 1.44/0.54  fof(f140,plain,(
% 1.44/0.54    k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)),
% 1.44/0.54    inference(resolution,[],[f139,f120])).
% 1.44/0.54  fof(f120,plain,(
% 1.44/0.54    r1_partfun1(sK1,sK2) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)),
% 1.44/0.54    inference(resolution,[],[f119,f49])).
% 1.44/0.54  fof(f49,plain,(
% 1.44/0.54    v1_relat_1(sK1)),
% 1.44/0.54    inference(resolution,[],[f45,f32])).
% 1.44/0.54  fof(f32,plain,(
% 1.44/0.54    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.44/0.54    inference(cnf_transformation,[],[f25])).
% 1.44/0.54  fof(f25,plain,(
% 1.44/0.54    (((k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) & r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1))) | ~r1_partfun1(sK1,sK2)) & (! [X4] : (k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,k1_relset_1(sK0,sK0,sK1))) | r1_partfun1(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK1)),
% 1.44/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f24,f23,f22])).
% 1.44/0.54  fof(f22,plain,(
% 1.44/0.54    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => (? [X2] : ((? [X3] : (k1_funct_1(X2,X3) != k1_funct_1(sK1,X3) & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1))) | ~r1_partfun1(sK1,X2)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(sK1,X4) | ~r2_hidden(X4,k1_relset_1(sK0,sK0,sK1))) | r1_partfun1(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK1))),
% 1.44/0.54    introduced(choice_axiom,[])).
% 1.44/0.54  fof(f23,plain,(
% 1.44/0.54    ? [X2] : ((? [X3] : (k1_funct_1(X2,X3) != k1_funct_1(sK1,X3) & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1))) | ~r1_partfun1(sK1,X2)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(sK1,X4) | ~r2_hidden(X4,k1_relset_1(sK0,sK0,sK1))) | r1_partfun1(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => ((? [X3] : (k1_funct_1(sK1,X3) != k1_funct_1(sK2,X3) & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1))) | ~r1_partfun1(sK1,sK2)) & (! [X4] : (k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,k1_relset_1(sK0,sK0,sK1))) | r1_partfun1(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 1.44/0.54    introduced(choice_axiom,[])).
% 1.44/0.54  fof(f24,plain,(
% 1.44/0.54    ? [X3] : (k1_funct_1(sK1,X3) != k1_funct_1(sK2,X3) & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1))) => (k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) & r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1)))),
% 1.44/0.54    introduced(choice_axiom,[])).
% 1.44/0.54  fof(f21,plain,(
% 1.44/0.54    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 1.44/0.54    inference(rectify,[],[f20])).
% 1.44/0.54  fof(f20,plain,(
% 1.44/0.54    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 1.44/0.54    inference(flattening,[],[f19])).
% 1.44/0.54  fof(f19,plain,(
% 1.44/0.54    ? [X0,X1] : (? [X2] : (((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 1.44/0.54    inference(nnf_transformation,[],[f10])).
% 1.44/0.54  fof(f10,plain,(
% 1.44/0.54    ? [X0,X1] : (? [X2] : ((r1_partfun1(X1,X2) <~> ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 1.44/0.54    inference(flattening,[],[f9])).
% 1.44/0.54  fof(f9,plain,(
% 1.44/0.54    ? [X0,X1] : (? [X2] : ((r1_partfun1(X1,X2) <~> ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)))),
% 1.44/0.54    inference(ennf_transformation,[],[f8])).
% 1.44/0.54  fof(f8,negated_conjecture,(
% 1.44/0.54    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) <=> ! [X3] : (r2_hidden(X3,k1_relset_1(X0,X0,X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)))))),
% 1.44/0.54    inference(negated_conjecture,[],[f7])).
% 1.44/0.54  fof(f7,conjecture,(
% 1.44/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) <=> ! [X3] : (r2_hidden(X3,k1_relset_1(X0,X0,X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)))))),
% 1.44/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_2)).
% 1.44/0.54  fof(f45,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f16])).
% 1.44/0.54  fof(f16,plain,(
% 1.44/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.54    inference(ennf_transformation,[],[f2])).
% 1.44/0.54  fof(f2,axiom,(
% 1.44/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.44/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.44/0.54  fof(f119,plain,(
% 1.44/0.54    ~v1_relat_1(sK1) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | r1_partfun1(sK1,sK2)),
% 1.44/0.54    inference(resolution,[],[f118,f50])).
% 1.44/0.54  fof(f50,plain,(
% 1.44/0.54    v1_relat_1(sK2)),
% 1.44/0.54    inference(resolution,[],[f45,f35])).
% 1.44/0.54  fof(f35,plain,(
% 1.44/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.44/0.54    inference(cnf_transformation,[],[f25])).
% 1.44/0.54  fof(f118,plain,(
% 1.44/0.54    ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | r1_partfun1(sK1,sK2)),
% 1.44/0.54    inference(resolution,[],[f117,f53])).
% 1.44/0.54  fof(f53,plain,(
% 1.44/0.54    v4_relat_1(sK1,sK0)),
% 1.44/0.54    inference(resolution,[],[f47,f32])).
% 1.44/0.54  fof(f47,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f18])).
% 1.44/0.54  fof(f18,plain,(
% 1.44/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.54    inference(ennf_transformation,[],[f3])).
% 1.44/0.54  fof(f3,axiom,(
% 1.44/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.44/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.44/0.54  fof(f117,plain,(
% 1.44/0.54    ~v4_relat_1(sK1,sK0) | r1_partfun1(sK1,sK2) | ~v1_relat_1(sK1) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | ~v1_relat_1(sK2)),
% 1.44/0.54    inference(duplicate_literal_removal,[],[f116])).
% 1.44/0.54  fof(f116,plain,(
% 1.44/0.54    ~v1_relat_1(sK2) | r1_partfun1(sK1,sK2) | ~v1_relat_1(sK1) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | ~v4_relat_1(sK1,sK0) | ~v1_relat_1(sK1)),
% 1.44/0.54    inference(resolution,[],[f115,f42])).
% 1.44/0.54  fof(f42,plain,(
% 1.44/0.54    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f30])).
% 1.44/0.54  fof(f30,plain,(
% 1.44/0.54    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.44/0.54    inference(nnf_transformation,[],[f13])).
% 1.44/0.54  fof(f13,plain,(
% 1.44/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.44/0.54    inference(ennf_transformation,[],[f1])).
% 1.44/0.54  fof(f1,axiom,(
% 1.44/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.44/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.44/0.54  fof(f115,plain,(
% 1.44/0.54    ~r1_tarski(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK2) | r1_partfun1(sK1,sK2) | ~v1_relat_1(sK1) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)),
% 1.44/0.54    inference(resolution,[],[f113,f31])).
% 1.44/0.54  fof(f31,plain,(
% 1.44/0.54    v1_funct_1(sK1)),
% 1.44/0.54    inference(cnf_transformation,[],[f25])).
% 1.44/0.54  fof(f113,plain,(
% 1.44/0.54    ~v1_funct_1(sK1) | ~r1_tarski(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK2) | r1_partfun1(sK1,sK2) | ~v1_relat_1(sK1) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)),
% 1.44/0.54    inference(resolution,[],[f112,f33])).
% 1.44/0.54  fof(f33,plain,(
% 1.44/0.54    v1_funct_1(sK2)),
% 1.44/0.54    inference(cnf_transformation,[],[f25])).
% 1.44/0.54  fof(f112,plain,(
% 1.44/0.54    ~v1_funct_1(sK2) | r1_partfun1(sK1,sK2) | ~r1_tarski(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)),
% 1.44/0.54    inference(forward_demodulation,[],[f111,f66])).
% 1.44/0.54  fof(f66,plain,(
% 1.44/0.54    sK0 = k1_relat_1(sK2)),
% 1.44/0.54    inference(resolution,[],[f64,f35])).
% 1.44/0.54  fof(f64,plain,(
% 1.44/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 = k1_relat_1(sK2)),
% 1.44/0.54    inference(resolution,[],[f63,f33])).
% 1.44/0.54  fof(f63,plain,(
% 1.44/0.54    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 = k1_relat_1(sK2)),
% 1.44/0.54    inference(forward_demodulation,[],[f62,f58])).
% 1.44/0.54  fof(f58,plain,(
% 1.44/0.54    k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2)),
% 1.44/0.54    inference(resolution,[],[f46,f35])).
% 1.44/0.54  fof(f46,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f17])).
% 1.44/0.54  fof(f17,plain,(
% 1.44/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.44/0.54    inference(ennf_transformation,[],[f4])).
% 1.44/0.54  fof(f4,axiom,(
% 1.44/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.44/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.44/0.54  fof(f62,plain,(
% 1.44/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 = k1_relset_1(sK0,sK0,sK2) | ~v1_funct_1(sK2)),
% 1.44/0.54    inference(resolution,[],[f44,f34])).
% 1.44/0.54  fof(f34,plain,(
% 1.44/0.54    v1_funct_2(sK2,sK0,sK0)),
% 1.44/0.54    inference(cnf_transformation,[],[f25])).
% 1.44/0.54  fof(f44,plain,(
% 1.44/0.54    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0 | ~v1_funct_1(X1)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f15])).
% 1.44/0.54  fof(f15,plain,(
% 1.44/0.54    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.44/0.54    inference(flattening,[],[f14])).
% 1.44/0.54  fof(f14,plain,(
% 1.44/0.54    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.44/0.54    inference(ennf_transformation,[],[f6])).
% 1.44/0.54  fof(f6,axiom,(
% 1.44/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 1.44/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).
% 1.44/0.54  fof(f111,plain,(
% 1.44/0.54    r1_partfun1(sK1,sK2) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)),
% 1.44/0.54    inference(trivial_inequality_removal,[],[f110])).
% 1.44/0.54  fof(f110,plain,(
% 1.44/0.54    k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK1,sK4(sK1,sK2)) | r1_partfun1(sK1,sK2) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)),
% 1.44/0.54    inference(superposition,[],[f41,f109])).
% 1.44/0.54  fof(f109,plain,(
% 1.44/0.54    k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)),
% 1.44/0.54    inference(duplicate_literal_removal,[],[f108])).
% 1.44/0.54  fof(f108,plain,(
% 1.44/0.54    k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))),
% 1.44/0.54    inference(resolution,[],[f106,f93])).
% 1.44/0.54  fof(f93,plain,(
% 1.44/0.54    r1_partfun1(sK1,sK2) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))),
% 1.44/0.54    inference(resolution,[],[f92,f49])).
% 1.44/0.54  fof(f92,plain,(
% 1.44/0.54    ~v1_relat_1(sK1) | r1_partfun1(sK1,sK2) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))),
% 1.44/0.54    inference(resolution,[],[f91,f50])).
% 1.44/0.54  fof(f91,plain,(
% 1.44/0.54    ~v1_relat_1(sK2) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | r1_partfun1(sK1,sK2) | ~v1_relat_1(sK1)),
% 1.44/0.54    inference(resolution,[],[f90,f53])).
% 1.44/0.54  fof(f90,plain,(
% 1.44/0.54    ~v4_relat_1(sK1,sK0) | ~v1_relat_1(sK2) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | r1_partfun1(sK1,sK2) | ~v1_relat_1(sK1)),
% 1.44/0.54    inference(resolution,[],[f88,f42])).
% 1.44/0.54  fof(f88,plain,(
% 1.44/0.54    ~r1_tarski(k1_relat_1(sK1),sK0) | r1_partfun1(sK1,sK2) | ~v1_relat_1(sK2) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))),
% 1.44/0.54    inference(resolution,[],[f77,f33])).
% 1.44/0.54  fof(f77,plain,(
% 1.44/0.54    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | r1_partfun1(sK1,sK2) | ~r1_tarski(k1_relat_1(sK1),sK0) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))),
% 1.44/0.54    inference(duplicate_literal_removal,[],[f76])).
% 1.44/0.54  fof(f76,plain,(
% 1.44/0.54    ~r1_tarski(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK2) | r1_partfun1(sK1,sK2) | ~v1_funct_1(sK2) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | r1_partfun1(sK1,sK2)),
% 1.44/0.54    inference(superposition,[],[f74,f66])).
% 1.44/0.54  fof(f74,plain,(
% 1.44/0.54    ( ! [X0] : (~r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) | ~v1_relat_1(X0) | r1_partfun1(sK1,X0) | ~v1_funct_1(X0) | k1_funct_1(sK1,sK4(sK1,X0)) = k1_funct_1(sK2,sK4(sK1,X0)) | r1_partfun1(sK1,sK2)) )),
% 1.44/0.54    inference(resolution,[],[f73,f49])).
% 1.44/0.54  fof(f73,plain,(
% 1.44/0.54    ( ! [X0] : (~v1_relat_1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r1_partfun1(sK1,X0) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) | k1_funct_1(sK1,sK4(sK1,X0)) = k1_funct_1(sK2,sK4(sK1,X0)) | r1_partfun1(sK1,sK2)) )),
% 1.44/0.54    inference(resolution,[],[f65,f31])).
% 1.44/0.54  fof(f65,plain,(
% 1.44/0.54    ( ! [X0] : (~v1_funct_1(sK1) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r1_partfun1(sK1,X0) | ~v1_relat_1(sK1) | k1_funct_1(sK1,sK4(sK1,X0)) = k1_funct_1(sK2,sK4(sK1,X0)) | r1_partfun1(sK1,sK2)) )),
% 1.44/0.54    inference(resolution,[],[f40,f59])).
% 1.44/0.54  fof(f59,plain,(
% 1.44/0.54    ( ! [X4] : (~r2_hidden(X4,k1_relat_1(sK1)) | k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4) | r1_partfun1(sK1,sK2)) )),
% 1.44/0.54    inference(backward_demodulation,[],[f36,f57])).
% 1.44/0.54  fof(f57,plain,(
% 1.44/0.54    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)),
% 1.44/0.54    inference(resolution,[],[f46,f32])).
% 1.44/0.54  fof(f36,plain,(
% 1.44/0.54    ( ! [X4] : (k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,k1_relset_1(sK0,sK0,sK1)) | r1_partfun1(sK1,sK2)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f25])).
% 1.44/0.54  fof(f40,plain,(
% 1.44/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | r1_partfun1(X0,X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f29])).
% 1.44/0.54  fof(f29,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.44/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).
% 1.44/0.54  fof(f28,plain,(
% 1.44/0.54    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 1.44/0.54    introduced(choice_axiom,[])).
% 1.44/0.54  fof(f27,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.44/0.54    inference(rectify,[],[f26])).
% 1.44/0.54  fof(f26,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.44/0.54    inference(nnf_transformation,[],[f12])).
% 1.44/0.54  fof(f12,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : ((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.44/0.54    inference(flattening,[],[f11])).
% 1.44/0.54  fof(f11,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.44/0.54    inference(ennf_transformation,[],[f5])).
% 1.44/0.54  fof(f5,axiom,(
% 1.44/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) => (r1_partfun1(X0,X1) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2))))))),
% 1.44/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_partfun1)).
% 1.44/0.54  fof(f106,plain,(
% 1.44/0.54    ~r1_partfun1(sK1,sK2) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))),
% 1.44/0.54    inference(resolution,[],[f105,f60])).
% 1.44/0.54  fof(f60,plain,(
% 1.44/0.54    r2_hidden(sK3,k1_relat_1(sK1)) | ~r1_partfun1(sK1,sK2)),
% 1.44/0.54    inference(backward_demodulation,[],[f37,f57])).
% 1.44/0.54  fof(f37,plain,(
% 1.44/0.54    r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1)) | ~r1_partfun1(sK1,sK2)),
% 1.44/0.54    inference(cnf_transformation,[],[f25])).
% 1.44/0.54  fof(f105,plain,(
% 1.44/0.54    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0)) )),
% 1.44/0.54    inference(resolution,[],[f104,f49])).
% 1.44/0.54  fof(f104,plain,(
% 1.44/0.54    ( ! [X0] : (~v1_relat_1(sK1) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0)) )),
% 1.44/0.54    inference(resolution,[],[f103,f50])).
% 1.44/0.54  fof(f103,plain,(
% 1.44/0.54    ( ! [X0] : (~v1_relat_1(sK2) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | ~v1_relat_1(sK1) | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0)) )),
% 1.44/0.54    inference(resolution,[],[f102,f53])).
% 1.44/0.54  fof(f102,plain,(
% 1.44/0.54    ( ! [X0] : (~v4_relat_1(sK1,sK0) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK2) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | ~v1_relat_1(sK1) | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0)) )),
% 1.44/0.54    inference(duplicate_literal_removal,[],[f101])).
% 1.44/0.54  fof(f101,plain,(
% 1.44/0.54    ( ! [X0] : (k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK2) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | ~v1_relat_1(sK1) | ~v4_relat_1(sK1,sK0) | ~v1_relat_1(sK1)) )),
% 1.44/0.54    inference(resolution,[],[f100,f42])).
% 1.44/0.55  % (23617)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.44/0.55  % (23610)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 1.44/0.55  % (23618)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.44/0.55  % (23623)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.44/0.55  % (23629)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.44/0.55  % (23608)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 1.44/0.55  % (23619)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.44/0.56  fof(f100,plain,(
% 1.44/0.56    ( ! [X0] : (~r1_tarski(k1_relat_1(sK1),sK0) | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK2) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | ~v1_relat_1(sK1)) )),
% 1.44/0.56    inference(resolution,[],[f99,f31])).
% 1.44/0.56  fof(f99,plain,(
% 1.44/0.56    ( ! [X0] : (~v1_funct_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0) | ~r1_tarski(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK2) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | ~v1_relat_1(sK1)) )),
% 1.44/0.56    inference(resolution,[],[f96,f33])).
% 1.44/0.56  fof(f96,plain,(
% 1.44/0.56    ( ! [X0] : (~v1_funct_1(sK2) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0) | ~r1_tarski(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.44/0.56    inference(forward_demodulation,[],[f95,f66])).
% 1.44/0.56  fof(f95,plain,(
% 1.44/0.56    ( ! [X0] : (k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.44/0.56    inference(resolution,[],[f93,f39])).
% 1.44/0.56  fof(f39,plain,(
% 1.44/0.56    ( ! [X0,X3,X1] : (~r1_partfun1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X1,X3) = k1_funct_1(X0,X3) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f29])).
% 1.44/0.56  fof(f41,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | r1_partfun1(X0,X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f29])).
% 1.44/0.56  fof(f139,plain,(
% 1.44/0.56    ~r1_partfun1(sK1,sK2) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)),
% 1.44/0.56    inference(duplicate_literal_removal,[],[f137])).
% 1.44/0.56  fof(f137,plain,(
% 1.44/0.56    k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | ~r1_partfun1(sK1,sK2)),
% 1.44/0.56    inference(resolution,[],[f136,f60])).
% 1.44/0.56  fof(f136,plain,(
% 1.44/0.56    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0)) )),
% 1.44/0.56    inference(resolution,[],[f135,f49])).
% 1.44/0.56  fof(f135,plain,(
% 1.44/0.56    ( ! [X0] : (~v1_relat_1(sK1) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0)) )),
% 1.44/0.56    inference(resolution,[],[f131,f50])).
% 1.44/0.56  fof(f131,plain,(
% 1.44/0.56    ( ! [X0] : (~v1_relat_1(sK2) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | ~v1_relat_1(sK1) | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0)) )),
% 1.44/0.56    inference(resolution,[],[f130,f53])).
% 1.44/0.56  fof(f130,plain,(
% 1.44/0.56    ( ! [X0] : (~v4_relat_1(sK1,sK0) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK2) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | ~v1_relat_1(sK1) | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0)) )),
% 1.44/0.56    inference(duplicate_literal_removal,[],[f129])).
% 1.44/0.56  fof(f129,plain,(
% 1.44/0.56    ( ! [X0] : (k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK2) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | ~v1_relat_1(sK1) | ~v4_relat_1(sK1,sK0) | ~v1_relat_1(sK1)) )),
% 1.44/0.56    inference(resolution,[],[f128,f42])).
% 1.44/0.56  fof(f128,plain,(
% 1.44/0.56    ( ! [X0] : (~r1_tarski(k1_relat_1(sK1),sK0) | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK2) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | ~v1_relat_1(sK1)) )),
% 1.44/0.56    inference(resolution,[],[f127,f31])).
% 1.44/0.56  fof(f127,plain,(
% 1.44/0.56    ( ! [X0] : (~v1_funct_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0) | ~r1_tarski(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK2) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | ~v1_relat_1(sK1)) )),
% 1.44/0.56    inference(resolution,[],[f126,f33])).
% 1.44/0.56  fof(f126,plain,(
% 1.44/0.56    ( ! [X0] : (~v1_funct_1(sK2) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0) | ~r1_tarski(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.44/0.56    inference(forward_demodulation,[],[f124,f66])).
% 1.44/0.56  fof(f124,plain,(
% 1.44/0.56    ( ! [X0] : (k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK2,X0) = k1_funct_1(sK1,X0) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.44/0.56    inference(resolution,[],[f120,f39])).
% 1.44/0.56  fof(f38,plain,(
% 1.44/0.56    ~r1_partfun1(sK1,sK2) | k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)),
% 1.44/0.56    inference(cnf_transformation,[],[f25])).
% 1.44/0.56  fof(f156,plain,(
% 1.44/0.56    r1_partfun1(sK1,sK2)),
% 1.44/0.56    inference(resolution,[],[f155,f49])).
% 1.44/0.56  fof(f155,plain,(
% 1.44/0.56    ~v1_relat_1(sK1) | r1_partfun1(sK1,sK2)),
% 1.44/0.56    inference(resolution,[],[f154,f50])).
% 1.44/0.56  fof(f154,plain,(
% 1.44/0.56    ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | r1_partfun1(sK1,sK2)),
% 1.44/0.56    inference(resolution,[],[f153,f53])).
% 1.44/0.56  fof(f153,plain,(
% 1.44/0.56    ~v4_relat_1(sK1,sK0) | r1_partfun1(sK1,sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK2)),
% 1.44/0.56    inference(duplicate_literal_removal,[],[f152])).
% 1.58/0.56  fof(f152,plain,(
% 1.58/0.56    ~v1_relat_1(sK2) | r1_partfun1(sK1,sK2) | ~v1_relat_1(sK1) | ~v4_relat_1(sK1,sK0) | ~v1_relat_1(sK1)),
% 1.58/0.56    inference(resolution,[],[f151,f42])).
% 1.58/0.56  fof(f151,plain,(
% 1.58/0.56    ~r1_tarski(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK2) | r1_partfun1(sK1,sK2) | ~v1_relat_1(sK1)),
% 1.58/0.56    inference(resolution,[],[f150,f31])).
% 1.58/0.56  fof(f150,plain,(
% 1.58/0.56    ~v1_funct_1(sK1) | ~r1_tarski(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK2) | r1_partfun1(sK1,sK2) | ~v1_relat_1(sK1)),
% 1.58/0.56    inference(resolution,[],[f149,f33])).
% 1.58/0.56  fof(f149,plain,(
% 1.58/0.56    ~v1_funct_1(sK2) | r1_partfun1(sK1,sK2) | ~r1_tarski(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.58/0.56    inference(forward_demodulation,[],[f148,f66])).
% 1.58/0.56  fof(f148,plain,(
% 1.58/0.56    r1_partfun1(sK1,sK2) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.58/0.56    inference(trivial_inequality_removal,[],[f147])).
% 1.58/0.56  fof(f147,plain,(
% 1.58/0.56    k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK1,sK4(sK1,sK2)) | r1_partfun1(sK1,sK2) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.58/0.56    inference(superposition,[],[f41,f145])).
% 1.58/0.56  fof(f145,plain,(
% 1.58/0.56    k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))),
% 1.58/0.56    inference(trivial_inequality_removal,[],[f144])).
% 1.58/0.56  fof(f144,plain,(
% 1.58/0.56    k1_funct_1(sK1,sK3) != k1_funct_1(sK1,sK3) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))),
% 1.58/0.56    inference(backward_demodulation,[],[f94,f142])).
% 1.58/0.56  fof(f94,plain,(
% 1.58/0.56    k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))),
% 1.58/0.56    inference(resolution,[],[f93,f38])).
% 1.58/0.56  % SZS output end Proof for theBenchmark
% 1.58/0.56  % (23615)------------------------------
% 1.58/0.56  % (23615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.56  % (23615)Termination reason: Refutation
% 1.58/0.56  
% 1.58/0.56  % (23615)Memory used [KB]: 1663
% 1.58/0.56  % (23615)Time elapsed: 0.117 s
% 1.58/0.56  % (23615)------------------------------
% 1.58/0.56  % (23615)------------------------------
% 1.58/0.56  % (23612)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.58/0.56  % (23605)Success in time 0.204 s
%------------------------------------------------------------------------------
