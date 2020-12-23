%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  106 (3381 expanded)
%              Number of leaves         :   13 ( 981 expanded)
%              Depth                    :   39
%              Number of atoms          :  442 (26576 expanded)
%              Number of equality atoms :   92 (4834 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f197,plain,(
    $false ),
    inference(subsumption_resolution,[],[f196,f180])).

fof(f180,plain,(
    k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f42,f178])).

fof(f178,plain,(
    r1_partfun1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f177,f78])).

fof(f78,plain,(
    r1_tarski(k1_relat_1(sK1),sK0) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,
    ( r1_tarski(k1_relat_1(sK1),sK0)
    | r1_tarski(k1_relat_1(sK1),sK0) ),
    inference(resolution,[],[f74,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f74,plain,(
    ! [X0] :
      ( r2_hidden(sK5(k1_relat_1(sK1),X0),sK0)
      | r1_tarski(k1_relat_1(sK1),X0) ) ),
    inference(resolution,[],[f72,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X2))
      | r2_hidden(sK5(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f46,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f72,plain,(
    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f70,f66])).

fof(f66,plain,(
    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(resolution,[],[f51,f36])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f27,f26,f25])).

fof(f25,plain,
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

fof(f26,plain,
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

fof(f27,plain,
    ( ? [X3] :
        ( k1_funct_1(sK1,X3) != k1_funct_1(sK2,X3)
        & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1)) )
   => ( k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
      & r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_2)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f70,plain,(
    m1_subset_1(k1_relset_1(sK0,sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f52,f36])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f177,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),sK0)
    | r1_partfun1(sK1,sK2) ),
    inference(forward_demodulation,[],[f176,f86])).

fof(f86,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f67,f85])).

fof(f85,plain,(
    sK0 = k1_relset_1(sK0,sK0,sK2) ),
    inference(subsumption_resolution,[],[f84,f37])).

fof(f37,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f84,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f83,f39])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f83,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f47,f38])).

fof(f38,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(f67,plain,(
    k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f51,f39])).

fof(f176,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | r1_partfun1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f175,f56])).

fof(f56,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f50,f39])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f175,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | r1_partfun1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f171,f147])).

fof(f147,plain,(
    k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f145,f117])).

fof(f117,plain,
    ( k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(resolution,[],[f115,f42])).

fof(f115,plain,
    ( r1_partfun1(sK1,sK2)
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f114,f78])).

fof(f114,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),sK0)
    | r1_partfun1(sK1,sK2)
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(forward_demodulation,[],[f113,f86])).

fof(f113,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | r1_partfun1(sK1,sK2)
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f110,f56])).

fof(f110,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | r1_partfun1(sK1,sK2)
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | r1_partfun1(sK1,sK2)
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
    | r1_partfun1(sK1,sK2) ),
    inference(resolution,[],[f102,f37])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | r1_partfun1(sK1,X0)
      | k1_funct_1(sK1,sK4(sK1,X0)) = k1_funct_1(sK2,sK4(sK1,X0))
      | r1_partfun1(sK1,sK2) ) ),
    inference(resolution,[],[f97,f68])).

fof(f68,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_relat_1(sK1))
      | k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4)
      | r1_partfun1(sK1,sK2) ) ),
    inference(backward_demodulation,[],[f40,f66])).

fof(f40,plain,(
    ! [X4] :
      ( k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4)
      | ~ r2_hidden(X4,k1_relset_1(sK0,sK0,sK1))
      | r1_partfun1(sK1,sK2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f97,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK1,X0),k1_relat_1(sK1))
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r1_partfun1(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f95,f55])).

fof(f55,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f50,f36])).

fof(f95,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK1,X0),k1_relat_1(sK1))
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r1_partfun1(sK1,X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f44,f35])).

fof(f35,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_partfun1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f14])).

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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_partfun1)).

fof(f145,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
    | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
    | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(resolution,[],[f124,f116])).

fof(f116,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(resolution,[],[f115,f69])).

fof(f69,plain,
    ( ~ r1_partfun1(sK1,sK2)
    | r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f41,f66])).

fof(f41,plain,
    ( ~ r1_partfun1(sK1,sK2)
    | r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f124,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f123,f78])).

fof(f123,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK1),sK0)
      | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) ) ),
    inference(forward_demodulation,[],[f122,f86])).

fof(f122,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f121,f55])).

fof(f121,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f120,f35])).

fof(f120,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f119,f56])).

fof(f119,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f118,f37])).

fof(f118,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f115,f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_partfun1(X0,X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X1,X3) = k1_funct_1(X0,X3)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f171,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | r1_partfun1(sK1,sK2) ),
    inference(resolution,[],[f160,f37])).

fof(f160,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(X0))
      | k1_funct_1(sK1,sK4(sK1,X0)) != k1_funct_1(X0,sK4(sK1,X0))
      | ~ v1_relat_1(X0)
      | r1_partfun1(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f158,f55])).

fof(f158,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK4(sK1,X0)) != k1_funct_1(X0,sK4(sK1,X0))
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r1_partfun1(sK1,X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f45,f35])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_partfun1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f42,plain,
    ( ~ r1_partfun1(sK1,sK2)
    | k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f196,plain,(
    k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) ),
    inference(resolution,[],[f189,f179])).

fof(f179,plain,(
    r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f69,f178])).

fof(f189,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f188,f78])).

fof(f188,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK1),sK0)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) ) ),
    inference(forward_demodulation,[],[f187,f86])).

fof(f187,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f186,f55])).

fof(f186,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f185,f35])).

fof(f185,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f184,f56])).

fof(f184,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f183,f37])).

fof(f183,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f178,f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n015.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 11:32:53 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.54  % (4537)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (4548)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (4539)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (4537)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (4552)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (4544)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (4546)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (4540)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (4540)Refutation not found, incomplete strategy% (4540)------------------------------
% 0.21/0.56  % (4540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (4540)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (4540)Memory used [KB]: 10746
% 0.21/0.56  % (4540)Time elapsed: 0.143 s
% 0.21/0.56  % (4540)------------------------------
% 0.21/0.56  % (4540)------------------------------
% 1.41/0.56  % SZS output start Proof for theBenchmark
% 1.41/0.56  fof(f197,plain,(
% 1.41/0.56    $false),
% 1.41/0.56    inference(subsumption_resolution,[],[f196,f180])).
% 1.41/0.56  fof(f180,plain,(
% 1.41/0.56    k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)),
% 1.41/0.56    inference(subsumption_resolution,[],[f42,f178])).
% 1.41/0.56  fof(f178,plain,(
% 1.41/0.56    r1_partfun1(sK1,sK2)),
% 1.41/0.56    inference(subsumption_resolution,[],[f177,f78])).
% 1.41/0.56  fof(f78,plain,(
% 1.41/0.56    r1_tarski(k1_relat_1(sK1),sK0)),
% 1.41/0.56    inference(duplicate_literal_removal,[],[f76])).
% 1.41/0.56  fof(f76,plain,(
% 1.41/0.56    r1_tarski(k1_relat_1(sK1),sK0) | r1_tarski(k1_relat_1(sK1),sK0)),
% 1.41/0.56    inference(resolution,[],[f74,f49])).
% 1.41/0.56  fof(f49,plain,(
% 1.41/0.56    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f34])).
% 1.41/0.56  fof(f34,plain,(
% 1.41/0.56    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.41/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f33])).
% 1.41/0.56  fof(f33,plain,(
% 1.41/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.41/0.56    introduced(choice_axiom,[])).
% 1.41/0.56  fof(f18,plain,(
% 1.41/0.56    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.41/0.56    inference(ennf_transformation,[],[f10])).
% 1.41/0.56  fof(f10,plain,(
% 1.41/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.41/0.56    inference(unused_predicate_definition_removal,[],[f1])).
% 1.41/0.56  fof(f1,axiom,(
% 1.41/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.41/0.56  fof(f74,plain,(
% 1.41/0.56    ( ! [X0] : (r2_hidden(sK5(k1_relat_1(sK1),X0),sK0) | r1_tarski(k1_relat_1(sK1),X0)) )),
% 1.41/0.56    inference(resolution,[],[f72,f57])).
% 1.41/0.56  fof(f57,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X2)) | r2_hidden(sK5(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 1.41/0.56    inference(resolution,[],[f46,f48])).
% 1.41/0.56  fof(f48,plain,(
% 1.41/0.56    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f34])).
% 1.41/0.56  fof(f46,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.41/0.56    inference(cnf_transformation,[],[f15])).
% 1.41/0.56  fof(f15,plain,(
% 1.41/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.41/0.56    inference(ennf_transformation,[],[f2])).
% 1.41/0.56  fof(f2,axiom,(
% 1.41/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.41/0.56  fof(f72,plain,(
% 1.41/0.56    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))),
% 1.41/0.56    inference(forward_demodulation,[],[f70,f66])).
% 1.41/0.56  fof(f66,plain,(
% 1.41/0.56    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)),
% 1.41/0.56    inference(resolution,[],[f51,f36])).
% 1.41/0.56  fof(f36,plain,(
% 1.41/0.56    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.41/0.56    inference(cnf_transformation,[],[f28])).
% 1.41/0.56  fof(f28,plain,(
% 1.41/0.56    (((k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) & r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1))) | ~r1_partfun1(sK1,sK2)) & (! [X4] : (k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,k1_relset_1(sK0,sK0,sK1))) | r1_partfun1(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK1)),
% 1.41/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f27,f26,f25])).
% 1.41/0.56  fof(f25,plain,(
% 1.41/0.56    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => (? [X2] : ((? [X3] : (k1_funct_1(X2,X3) != k1_funct_1(sK1,X3) & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1))) | ~r1_partfun1(sK1,X2)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(sK1,X4) | ~r2_hidden(X4,k1_relset_1(sK0,sK0,sK1))) | r1_partfun1(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_1(sK1))),
% 1.41/0.56    introduced(choice_axiom,[])).
% 1.41/0.56  fof(f26,plain,(
% 1.41/0.56    ? [X2] : ((? [X3] : (k1_funct_1(X2,X3) != k1_funct_1(sK1,X3) & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1))) | ~r1_partfun1(sK1,X2)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(sK1,X4) | ~r2_hidden(X4,k1_relset_1(sK0,sK0,sK1))) | r1_partfun1(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => ((? [X3] : (k1_funct_1(sK1,X3) != k1_funct_1(sK2,X3) & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1))) | ~r1_partfun1(sK1,sK2)) & (! [X4] : (k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,k1_relset_1(sK0,sK0,sK1))) | r1_partfun1(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 1.41/0.56    introduced(choice_axiom,[])).
% 1.41/0.56  fof(f27,plain,(
% 1.41/0.56    ? [X3] : (k1_funct_1(sK1,X3) != k1_funct_1(sK2,X3) & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1))) => (k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) & r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1)))),
% 1.41/0.56    introduced(choice_axiom,[])).
% 1.41/0.56  fof(f24,plain,(
% 1.41/0.56    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X4] : (k1_funct_1(X1,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 1.41/0.56    inference(rectify,[],[f23])).
% 1.41/0.56  fof(f23,plain,(
% 1.41/0.56    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 1.41/0.56    inference(flattening,[],[f22])).
% 1.41/0.56  fof(f22,plain,(
% 1.41/0.56    ? [X0,X1] : (? [X2] : (((? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relset_1(X0,X0,X1))) | ~r1_partfun1(X1,X2)) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1))) | r1_partfun1(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 1.41/0.56    inference(nnf_transformation,[],[f12])).
% 1.41/0.56  fof(f12,plain,(
% 1.41/0.56    ? [X0,X1] : (? [X2] : ((r1_partfun1(X1,X2) <~> ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 1.41/0.56    inference(flattening,[],[f11])).
% 1.41/0.56  fof(f11,plain,(
% 1.41/0.56    ? [X0,X1] : (? [X2] : ((r1_partfun1(X1,X2) <~> ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)))),
% 1.41/0.56    inference(ennf_transformation,[],[f9])).
% 1.41/0.56  fof(f9,negated_conjecture,(
% 1.41/0.56    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) <=> ! [X3] : (r2_hidden(X3,k1_relset_1(X0,X0,X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)))))),
% 1.41/0.56    inference(negated_conjecture,[],[f8])).
% 1.41/0.56  fof(f8,conjecture,(
% 1.41/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) <=> ! [X3] : (r2_hidden(X3,k1_relset_1(X0,X0,X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)))))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_2)).
% 1.41/0.56  fof(f51,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f20])).
% 1.41/0.56  fof(f20,plain,(
% 1.41/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.56    inference(ennf_transformation,[],[f5])).
% 1.41/0.56  fof(f5,axiom,(
% 1.41/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.41/0.56  fof(f70,plain,(
% 1.41/0.56    m1_subset_1(k1_relset_1(sK0,sK0,sK1),k1_zfmisc_1(sK0))),
% 1.41/0.56    inference(resolution,[],[f52,f36])).
% 1.41/0.56  fof(f52,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 1.41/0.56    inference(cnf_transformation,[],[f21])).
% 1.41/0.56  fof(f21,plain,(
% 1.41/0.56    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.56    inference(ennf_transformation,[],[f4])).
% 1.41/0.56  fof(f4,axiom,(
% 1.41/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 1.41/0.56  fof(f177,plain,(
% 1.41/0.56    ~r1_tarski(k1_relat_1(sK1),sK0) | r1_partfun1(sK1,sK2)),
% 1.41/0.56    inference(forward_demodulation,[],[f176,f86])).
% 1.41/0.56  fof(f86,plain,(
% 1.41/0.56    sK0 = k1_relat_1(sK2)),
% 1.41/0.56    inference(backward_demodulation,[],[f67,f85])).
% 1.41/0.56  fof(f85,plain,(
% 1.41/0.56    sK0 = k1_relset_1(sK0,sK0,sK2)),
% 1.41/0.56    inference(subsumption_resolution,[],[f84,f37])).
% 1.41/0.56  fof(f37,plain,(
% 1.41/0.56    v1_funct_1(sK2)),
% 1.41/0.56    inference(cnf_transformation,[],[f28])).
% 1.41/0.56  fof(f84,plain,(
% 1.41/0.56    sK0 = k1_relset_1(sK0,sK0,sK2) | ~v1_funct_1(sK2)),
% 1.41/0.56    inference(subsumption_resolution,[],[f83,f39])).
% 1.41/0.56  fof(f39,plain,(
% 1.41/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.41/0.56    inference(cnf_transformation,[],[f28])).
% 1.41/0.56  fof(f83,plain,(
% 1.41/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 = k1_relset_1(sK0,sK0,sK2) | ~v1_funct_1(sK2)),
% 1.41/0.56    inference(resolution,[],[f47,f38])).
% 1.41/0.56  fof(f38,plain,(
% 1.41/0.56    v1_funct_2(sK2,sK0,sK0)),
% 1.41/0.56    inference(cnf_transformation,[],[f28])).
% 1.41/0.56  fof(f47,plain,(
% 1.41/0.56    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0 | ~v1_funct_1(X1)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f17])).
% 1.41/0.56  fof(f17,plain,(
% 1.41/0.56    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.41/0.56    inference(flattening,[],[f16])).
% 1.41/0.56  fof(f16,plain,(
% 1.41/0.56    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.41/0.56    inference(ennf_transformation,[],[f7])).
% 1.41/0.56  fof(f7,axiom,(
% 1.41/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).
% 1.41/0.56  fof(f67,plain,(
% 1.41/0.56    k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2)),
% 1.41/0.56    inference(resolution,[],[f51,f39])).
% 1.41/0.56  fof(f176,plain,(
% 1.41/0.56    ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | r1_partfun1(sK1,sK2)),
% 1.41/0.56    inference(subsumption_resolution,[],[f175,f56])).
% 1.41/0.56  fof(f56,plain,(
% 1.41/0.56    v1_relat_1(sK2)),
% 1.41/0.56    inference(resolution,[],[f50,f39])).
% 1.41/0.56  fof(f50,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f19])).
% 1.41/0.56  fof(f19,plain,(
% 1.41/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.56    inference(ennf_transformation,[],[f3])).
% 1.41/0.56  fof(f3,axiom,(
% 1.41/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.41/0.56  fof(f175,plain,(
% 1.41/0.56    ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | r1_partfun1(sK1,sK2)),
% 1.41/0.56    inference(subsumption_resolution,[],[f171,f147])).
% 1.41/0.56  fof(f147,plain,(
% 1.41/0.56    k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))),
% 1.41/0.56    inference(subsumption_resolution,[],[f145,f117])).
% 1.41/0.56  fof(f117,plain,(
% 1.41/0.56    k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))),
% 1.41/0.56    inference(resolution,[],[f115,f42])).
% 1.41/0.56  fof(f115,plain,(
% 1.41/0.56    r1_partfun1(sK1,sK2) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))),
% 1.41/0.56    inference(subsumption_resolution,[],[f114,f78])).
% 1.41/0.56  fof(f114,plain,(
% 1.41/0.56    ~r1_tarski(k1_relat_1(sK1),sK0) | r1_partfun1(sK1,sK2) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))),
% 1.41/0.56    inference(forward_demodulation,[],[f113,f86])).
% 1.41/0.56  fof(f113,plain,(
% 1.41/0.56    ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | r1_partfun1(sK1,sK2) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))),
% 1.41/0.56    inference(subsumption_resolution,[],[f110,f56])).
% 1.41/0.56  fof(f110,plain,(
% 1.41/0.56    ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | r1_partfun1(sK1,sK2) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))),
% 1.41/0.56    inference(duplicate_literal_removal,[],[f109])).
% 1.41/0.56  fof(f109,plain,(
% 1.41/0.56    ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | r1_partfun1(sK1,sK2) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | r1_partfun1(sK1,sK2)),
% 1.41/0.56    inference(resolution,[],[f102,f37])).
% 1.41/0.56  fof(f102,plain,(
% 1.41/0.56    ( ! [X0] : (~v1_funct_1(X0) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) | ~v1_relat_1(X0) | r1_partfun1(sK1,X0) | k1_funct_1(sK1,sK4(sK1,X0)) = k1_funct_1(sK2,sK4(sK1,X0)) | r1_partfun1(sK1,sK2)) )),
% 1.41/0.56    inference(resolution,[],[f97,f68])).
% 1.41/0.56  fof(f68,plain,(
% 1.41/0.56    ( ! [X4] : (~r2_hidden(X4,k1_relat_1(sK1)) | k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4) | r1_partfun1(sK1,sK2)) )),
% 1.41/0.56    inference(backward_demodulation,[],[f40,f66])).
% 1.41/0.56  fof(f40,plain,(
% 1.41/0.56    ( ! [X4] : (k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,k1_relset_1(sK0,sK0,sK1)) | r1_partfun1(sK1,sK2)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f28])).
% 1.41/0.56  fof(f97,plain,(
% 1.41/0.56    ( ! [X0] : (r2_hidden(sK4(sK1,X0),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r1_partfun1(sK1,X0)) )),
% 1.41/0.56    inference(subsumption_resolution,[],[f95,f55])).
% 1.41/0.56  fof(f55,plain,(
% 1.41/0.56    v1_relat_1(sK1)),
% 1.41/0.56    inference(resolution,[],[f50,f36])).
% 1.41/0.56  fof(f95,plain,(
% 1.41/0.56    ( ! [X0] : (r2_hidden(sK4(sK1,X0),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r1_partfun1(sK1,X0) | ~v1_relat_1(sK1)) )),
% 1.41/0.56    inference(resolution,[],[f44,f35])).
% 1.41/0.56  fof(f35,plain,(
% 1.41/0.56    v1_funct_1(sK1)),
% 1.41/0.56    inference(cnf_transformation,[],[f28])).
% 1.41/0.56  fof(f44,plain,(
% 1.41/0.56    ( ! [X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | r1_partfun1(X0,X1) | ~v1_relat_1(X0)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f32])).
% 1.41/0.56  fof(f32,plain,(
% 1.41/0.56    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.41/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).
% 1.41/0.56  fof(f31,plain,(
% 1.41/0.56    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 1.41/0.56    introduced(choice_axiom,[])).
% 1.41/0.56  fof(f30,plain,(
% 1.41/0.56    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.41/0.56    inference(rectify,[],[f29])).
% 1.41/0.56  fof(f29,plain,(
% 1.41/0.56    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.41/0.56    inference(nnf_transformation,[],[f14])).
% 1.41/0.56  fof(f14,plain,(
% 1.41/0.56    ! [X0] : (! [X1] : ((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.41/0.56    inference(flattening,[],[f13])).
% 1.41/0.56  fof(f13,plain,(
% 1.41/0.56    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.41/0.56    inference(ennf_transformation,[],[f6])).
% 1.41/0.56  fof(f6,axiom,(
% 1.41/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) => (r1_partfun1(X0,X1) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2))))))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_partfun1)).
% 1.41/0.56  fof(f145,plain,(
% 1.41/0.56    k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)),
% 1.41/0.56    inference(duplicate_literal_removal,[],[f144])).
% 1.41/0.56  fof(f144,plain,(
% 1.41/0.56    k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))),
% 1.41/0.56    inference(resolution,[],[f124,f116])).
% 1.41/0.56  fof(f116,plain,(
% 1.41/0.56    r2_hidden(sK3,k1_relat_1(sK1)) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))),
% 1.41/0.56    inference(resolution,[],[f115,f69])).
% 1.41/0.56  fof(f69,plain,(
% 1.41/0.56    ~r1_partfun1(sK1,sK2) | r2_hidden(sK3,k1_relat_1(sK1))),
% 1.41/0.56    inference(backward_demodulation,[],[f41,f66])).
% 1.41/0.56  fof(f41,plain,(
% 1.41/0.56    ~r1_partfun1(sK1,sK2) | r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1))),
% 1.41/0.56    inference(cnf_transformation,[],[f28])).
% 1.41/0.56  fof(f124,plain,(
% 1.41/0.56    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)) )),
% 1.41/0.56    inference(subsumption_resolution,[],[f123,f78])).
% 1.41/0.56  fof(f123,plain,(
% 1.41/0.56    ( ! [X0] : (~r1_tarski(k1_relat_1(sK1),sK0) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)) )),
% 1.41/0.56    inference(forward_demodulation,[],[f122,f86])).
% 1.41/0.56  fof(f122,plain,(
% 1.41/0.56    ( ! [X0] : (k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))) )),
% 1.41/0.56    inference(subsumption_resolution,[],[f121,f55])).
% 1.41/0.56  fof(f121,plain,(
% 1.41/0.56    ( ! [X0] : (k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | ~v1_relat_1(sK1)) )),
% 1.41/0.56    inference(subsumption_resolution,[],[f120,f35])).
% 1.41/0.56  fof(f120,plain,(
% 1.41/0.56    ( ! [X0] : (k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.41/0.56    inference(subsumption_resolution,[],[f119,f56])).
% 1.41/0.56  fof(f119,plain,(
% 1.41/0.56    ( ! [X0] : (k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.41/0.56    inference(subsumption_resolution,[],[f118,f37])).
% 1.41/0.56  fof(f118,plain,(
% 1.41/0.56    ( ! [X0] : (k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.41/0.56    inference(resolution,[],[f115,f43])).
% 1.41/0.56  fof(f43,plain,(
% 1.41/0.56    ( ! [X0,X3,X1] : (~r1_partfun1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X1,X3) = k1_funct_1(X0,X3) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f32])).
% 1.41/0.56  fof(f171,plain,(
% 1.41/0.56    ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) | ~v1_relat_1(sK2) | r1_partfun1(sK1,sK2)),
% 1.41/0.56    inference(resolution,[],[f160,f37])).
% 1.41/0.56  fof(f160,plain,(
% 1.41/0.56    ( ! [X0] : (~v1_funct_1(X0) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) | k1_funct_1(sK1,sK4(sK1,X0)) != k1_funct_1(X0,sK4(sK1,X0)) | ~v1_relat_1(X0) | r1_partfun1(sK1,X0)) )),
% 1.41/0.56    inference(subsumption_resolution,[],[f158,f55])).
% 1.41/0.56  fof(f158,plain,(
% 1.41/0.56    ( ! [X0] : (k1_funct_1(sK1,sK4(sK1,X0)) != k1_funct_1(X0,sK4(sK1,X0)) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r1_partfun1(sK1,X0) | ~v1_relat_1(sK1)) )),
% 1.41/0.56    inference(resolution,[],[f45,f35])).
% 1.41/0.56  fof(f45,plain,(
% 1.41/0.56    ( ! [X0,X1] : (~v1_funct_1(X0) | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | r1_partfun1(X0,X1) | ~v1_relat_1(X0)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f32])).
% 1.41/0.56  fof(f42,plain,(
% 1.41/0.56    ~r1_partfun1(sK1,sK2) | k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)),
% 1.41/0.56    inference(cnf_transformation,[],[f28])).
% 1.41/0.56  fof(f196,plain,(
% 1.41/0.56    k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)),
% 1.41/0.56    inference(resolution,[],[f189,f179])).
% 1.41/0.56  fof(f179,plain,(
% 1.41/0.56    r2_hidden(sK3,k1_relat_1(sK1))),
% 1.41/0.56    inference(subsumption_resolution,[],[f69,f178])).
% 1.41/0.56  fof(f189,plain,(
% 1.41/0.56    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)) )),
% 1.41/0.56    inference(subsumption_resolution,[],[f188,f78])).
% 1.41/0.56  fof(f188,plain,(
% 1.41/0.56    ( ! [X0] : (~r1_tarski(k1_relat_1(sK1),sK0) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)) )),
% 1.41/0.56    inference(forward_demodulation,[],[f187,f86])).
% 1.41/0.56  fof(f187,plain,(
% 1.41/0.56    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))) )),
% 1.41/0.56    inference(subsumption_resolution,[],[f186,f55])).
% 1.41/0.56  fof(f186,plain,(
% 1.41/0.56    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | ~v1_relat_1(sK1)) )),
% 1.41/0.56    inference(subsumption_resolution,[],[f185,f35])).
% 1.41/0.56  fof(f185,plain,(
% 1.41/0.56    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.41/0.56    inference(subsumption_resolution,[],[f184,f56])).
% 1.41/0.56  fof(f184,plain,(
% 1.41/0.56    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.41/0.56    inference(subsumption_resolution,[],[f183,f37])).
% 1.41/0.56  fof(f183,plain,(
% 1.41/0.56    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.41/0.56    inference(resolution,[],[f178,f43])).
% 1.41/0.56  % SZS output end Proof for theBenchmark
% 1.41/0.56  % (4537)------------------------------
% 1.41/0.56  % (4537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (4537)Termination reason: Refutation
% 1.41/0.56  
% 1.41/0.56  % (4537)Memory used [KB]: 6396
% 1.41/0.56  % (4537)Time elapsed: 0.113 s
% 1.41/0.56  % (4537)------------------------------
% 1.41/0.56  % (4537)------------------------------
% 1.41/0.57  % (4529)Success in time 0.2 s
%------------------------------------------------------------------------------
