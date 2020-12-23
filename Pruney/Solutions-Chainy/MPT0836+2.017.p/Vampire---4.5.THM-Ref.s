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
% DateTime   : Thu Dec  3 12:57:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 165 expanded)
%              Number of leaves         :   12 (  54 expanded)
%              Depth                    :   16
%              Number of atoms          :  216 ( 974 expanded)
%              Number of equality atoms :   12 (  49 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f96,plain,(
    $false ),
    inference(subsumption_resolution,[],[f95,f87])).

fof(f87,plain,(
    r2_hidden(sK3,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f86,f43])).

fof(f43,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f21,f24,f23,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f86,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | r2_hidden(k4_tarski(sK3,sK4),sK2) ),
    inference(subsumption_resolution,[],[f82,f28])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ! [X4] :
          ( ~ r2_hidden(k4_tarski(sK3,X4),sK2)
          | ~ m1_subset_1(X4,sK1) )
      | ~ r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) )
    & ( ( r2_hidden(k4_tarski(sK3,sK4),sK2)
        & m1_subset_1(sK4,sK1) )
      | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) )
    & m1_subset_1(sK3,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                  | ~ m1_subset_1(X4,X1) )
              | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
            & ( ? [X5] :
                  ( r2_hidden(k4_tarski(X3,X5),X2)
                  & m1_subset_1(X5,X1) )
              | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
            & m1_subset_1(X3,X0) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X3,X4),sK2)
                | ~ m1_subset_1(X4,sK1) )
            | ~ r2_hidden(X3,k1_relset_1(sK0,sK1,sK2)) )
          & ( ? [X5] :
                ( r2_hidden(k4_tarski(X3,X5),sK2)
                & m1_subset_1(X5,sK1) )
            | r2_hidden(X3,k1_relset_1(sK0,sK1,sK2)) )
          & m1_subset_1(X3,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X3] :
        ( ( ! [X4] :
              ( ~ r2_hidden(k4_tarski(X3,X4),sK2)
              | ~ m1_subset_1(X4,sK1) )
          | ~ r2_hidden(X3,k1_relset_1(sK0,sK1,sK2)) )
        & ( ? [X5] :
              ( r2_hidden(k4_tarski(X3,X5),sK2)
              & m1_subset_1(X5,sK1) )
          | r2_hidden(X3,k1_relset_1(sK0,sK1,sK2)) )
        & m1_subset_1(X3,sK0) )
   => ( ( ! [X4] :
            ( ~ r2_hidden(k4_tarski(sK3,X4),sK2)
            | ~ m1_subset_1(X4,sK1) )
        | ~ r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) )
      & ( ? [X5] :
            ( r2_hidden(k4_tarski(sK3,X5),sK2)
            & m1_subset_1(X5,sK1) )
        | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) )
      & m1_subset_1(sK3,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X5] :
        ( r2_hidden(k4_tarski(sK3,X5),sK2)
        & m1_subset_1(X5,sK1) )
   => ( r2_hidden(k4_tarski(sK3,sK4),sK2)
      & m1_subset_1(sK4,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                | ~ m1_subset_1(X4,X1) )
            | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
          & ( ? [X5] :
                ( r2_hidden(k4_tarski(X3,X5),X2)
                & m1_subset_1(X5,X1) )
            | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
          & m1_subset_1(X3,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                | ~ m1_subset_1(X4,X1) )
            | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
          & ( ? [X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
                & m1_subset_1(X4,X1) )
            | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
          & m1_subset_1(X3,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                | ~ m1_subset_1(X4,X1) )
            | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
          & ( ? [X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
                & m1_subset_1(X4,X1) )
            | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
          & m1_subset_1(X3,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
          <~> ? [X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
                & m1_subset_1(X4,X1) ) )
          & m1_subset_1(X3,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ! [X3] :
            ( m1_subset_1(X3,X0)
           => ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
            <=> ? [X4] :
                  ( r2_hidden(k4_tarski(X3,X4),X2)
                  & m1_subset_1(X4,X1) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,X0)
                   => ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                    <=> ? [X4] :
                          ( r2_hidden(k4_tarski(X3,X4),X2)
                          & m1_subset_1(X4,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                  <=> ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relset_1)).

fof(f82,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | r2_hidden(k4_tarski(sK3,sK4),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f31,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f31,plain,
    ( r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))
    | r2_hidden(k4_tarski(sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f95,plain,(
    ~ r2_hidden(sK3,k1_relat_1(sK2)) ),
    inference(resolution,[],[f94,f60])).

fof(f60,plain,(
    ! [X3] :
      ( r2_hidden(sK7(sK2,X3),sK1)
      | ~ r2_hidden(X3,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f44,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X0),sK2)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f41,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f34,f28])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f44,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f94,plain,(
    ~ r2_hidden(sK7(sK2,sK3),sK1) ),
    inference(resolution,[],[f93,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f93,plain,(
    ~ m1_subset_1(sK7(sK2,sK3),sK1) ),
    inference(subsumption_resolution,[],[f92,f87])).

fof(f92,plain,
    ( ~ m1_subset_1(sK7(sK2,sK3),sK1)
    | ~ r2_hidden(sK3,k1_relat_1(sK2)) ),
    inference(resolution,[],[f85,f44])).

fof(f85,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK3,X0),sK2)
      | ~ m1_subset_1(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f84,f43])).

fof(f84,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,k1_relat_1(sK2))
      | ~ m1_subset_1(X0,sK1)
      | ~ r2_hidden(k4_tarski(sK3,X0),sK2) ) ),
    inference(subsumption_resolution,[],[f81,f28])).

fof(f81,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,k1_relat_1(sK2))
      | ~ m1_subset_1(X0,sK1)
      | ~ r2_hidden(k4_tarski(sK3,X0),sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(superposition,[],[f32,f39])).

fof(f32,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))
      | ~ m1_subset_1(X4,sK1)
      | ~ r2_hidden(k4_tarski(sK3,X4),sK2) ) ),
    inference(cnf_transformation,[],[f19])).
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
% 0.14/0.34  % DateTime   : Tue Dec  1 13:58:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.44  % (5861)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.45  % (5849)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.45  % (5861)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f96,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(subsumption_resolution,[],[f95,f87])).
% 0.20/0.45  fof(f87,plain,(
% 0.20/0.45    r2_hidden(sK3,k1_relat_1(sK2))),
% 0.20/0.45    inference(subsumption_resolution,[],[f86,f43])).
% 0.20/0.45  fof(f43,plain,(
% 0.20/0.45    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 0.20/0.45    inference(equality_resolution,[],[f36])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.20/0.45    inference(cnf_transformation,[],[f25])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f21,f24,f23,f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.45    inference(rectify,[],[f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.45    inference(nnf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.20/0.45  fof(f86,plain,(
% 0.20/0.45    r2_hidden(sK3,k1_relat_1(sK2)) | r2_hidden(k4_tarski(sK3,sK4),sK2)),
% 0.20/0.45    inference(subsumption_resolution,[],[f82,f28])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.45    inference(cnf_transformation,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ((! [X4] : (~r2_hidden(k4_tarski(sK3,X4),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))) & ((r2_hidden(k4_tarski(sK3,sK4),sK2) & m1_subset_1(sK4,sK1)) | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))) & m1_subset_1(sK3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f18,f17,f16])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k1_relset_1(X0,X1,X2))) & (? [X5] : (r2_hidden(k4_tarski(X3,X5),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k1_relset_1(X0,X1,X2))) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(X3,k1_relset_1(sK0,sK1,sK2))) & (? [X5] : (r2_hidden(k4_tarski(X3,X5),sK2) & m1_subset_1(X5,sK1)) | r2_hidden(X3,k1_relset_1(sK0,sK1,sK2))) & m1_subset_1(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(X3,k1_relset_1(sK0,sK1,sK2))) & (? [X5] : (r2_hidden(k4_tarski(X3,X5),sK2) & m1_subset_1(X5,sK1)) | r2_hidden(X3,k1_relset_1(sK0,sK1,sK2))) & m1_subset_1(X3,sK0)) => ((! [X4] : (~r2_hidden(k4_tarski(sK3,X4),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))) & (? [X5] : (r2_hidden(k4_tarski(sK3,X5),sK2) & m1_subset_1(X5,sK1)) | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))) & m1_subset_1(sK3,sK0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ? [X5] : (r2_hidden(k4_tarski(sK3,X5),sK2) & m1_subset_1(X5,sK1)) => (r2_hidden(k4_tarski(sK3,sK4),sK2) & m1_subset_1(sK4,sK1))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k1_relset_1(X0,X1,X2))) & (? [X5] : (r2_hidden(k4_tarski(X3,X5),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k1_relset_1(X0,X1,X2))) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.45    inference(rectify,[],[f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k1_relset_1(X0,X1,X2))) & (? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)) | r2_hidden(X3,k1_relset_1(X0,X1,X2))) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.45    inference(flattening,[],[f13])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ? [X0,X1,X2] : (? [X3] : (((! [X4] : (~r2_hidden(k4_tarski(X3,X4),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k1_relset_1(X0,X1,X2))) & (? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)) | r2_hidden(X3,k1_relset_1(X0,X1,X2)))) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.45    inference(nnf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    ? [X0,X1,X2] : (? [X3] : ((r2_hidden(X3,k1_relset_1(X0,X1,X2)) <~> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1))) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.45    inference(ennf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,plain,(
% 0.20/0.45    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,k1_relset_1(X0,X1,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)))))),
% 0.20/0.45    inference(pure_predicate_removal,[],[f7])).
% 0.20/0.45  fof(f7,negated_conjecture,(
% 0.20/0.45    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,k1_relset_1(X0,X1,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)))))))),
% 0.20/0.45    inference(negated_conjecture,[],[f6])).
% 0.20/0.45  fof(f6,conjecture,(
% 0.20/0.45    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,k1_relset_1(X0,X1,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)))))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relset_1)).
% 0.20/0.45  fof(f82,plain,(
% 0.20/0.45    r2_hidden(sK3,k1_relat_1(sK2)) | r2_hidden(k4_tarski(sK3,sK4),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.45    inference(superposition,[],[f31,f39])).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.45    inference(ennf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) | r2_hidden(k4_tarski(sK3,sK4),sK2)),
% 0.20/0.45    inference(cnf_transformation,[],[f19])).
% 0.20/0.45  fof(f95,plain,(
% 0.20/0.45    ~r2_hidden(sK3,k1_relat_1(sK2))),
% 0.20/0.45    inference(resolution,[],[f94,f60])).
% 0.20/0.45  fof(f60,plain,(
% 0.20/0.45    ( ! [X3] : (r2_hidden(sK7(sK2,X3),sK1) | ~r2_hidden(X3,k1_relat_1(sK2))) )),
% 0.20/0.45    inference(resolution,[],[f44,f56])).
% 0.20/0.45  fof(f56,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X1,X0),sK2) | r2_hidden(X0,sK1)) )),
% 0.20/0.45    inference(resolution,[],[f41,f49])).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X0,sK2)) )),
% 0.20/0.45    inference(resolution,[],[f34,f28])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f27])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.20/0.45    inference(flattening,[],[f26])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.20/0.45    inference(nnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).
% 0.20/0.45  fof(f44,plain,(
% 0.20/0.45    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 0.20/0.45    inference(equality_resolution,[],[f35])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 0.20/0.45    inference(cnf_transformation,[],[f25])).
% 0.20/0.45  fof(f94,plain,(
% 0.20/0.45    ~r2_hidden(sK7(sK2,sK3),sK1)),
% 0.20/0.45    inference(resolution,[],[f93,f33])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.45  fof(f93,plain,(
% 0.20/0.45    ~m1_subset_1(sK7(sK2,sK3),sK1)),
% 0.20/0.45    inference(subsumption_resolution,[],[f92,f87])).
% 0.20/0.45  fof(f92,plain,(
% 0.20/0.45    ~m1_subset_1(sK7(sK2,sK3),sK1) | ~r2_hidden(sK3,k1_relat_1(sK2))),
% 0.20/0.45    inference(resolution,[],[f85,f44])).
% 0.20/0.45  fof(f85,plain,(
% 0.20/0.45    ( ! [X0] : (~r2_hidden(k4_tarski(sK3,X0),sK2) | ~m1_subset_1(X0,sK1)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f84,f43])).
% 0.20/0.45  fof(f84,plain,(
% 0.20/0.45    ( ! [X0] : (~r2_hidden(sK3,k1_relat_1(sK2)) | ~m1_subset_1(X0,sK1) | ~r2_hidden(k4_tarski(sK3,X0),sK2)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f81,f28])).
% 0.20/0.45  fof(f81,plain,(
% 0.20/0.45    ( ! [X0] : (~r2_hidden(sK3,k1_relat_1(sK2)) | ~m1_subset_1(X0,sK1) | ~r2_hidden(k4_tarski(sK3,X0),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 0.20/0.45    inference(superposition,[],[f32,f39])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ( ! [X4] : (~r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X4,sK1) | ~r2_hidden(k4_tarski(sK3,X4),sK2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f19])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (5861)------------------------------
% 0.20/0.45  % (5861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (5861)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (5861)Memory used [KB]: 1663
% 0.20/0.45  % (5861)Time elapsed: 0.009 s
% 0.20/0.45  % (5861)------------------------------
% 0.20/0.45  % (5861)------------------------------
% 0.20/0.45  % (5840)Success in time 0.099 s
%------------------------------------------------------------------------------
