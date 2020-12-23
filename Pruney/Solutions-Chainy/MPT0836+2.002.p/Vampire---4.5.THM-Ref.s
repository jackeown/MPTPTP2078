%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 375 expanded)
%              Number of leaves         :   19 ( 113 expanded)
%              Depth                    :   18
%              Number of atoms          :  291 (2112 expanded)
%              Number of equality atoms :   26 (  68 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f141,plain,(
    $false ),
    inference(subsumption_resolution,[],[f140,f79])).

fof(f79,plain,(
    r2_hidden(sK3,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f77,f68])).

fof(f68,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f35,f38,f37,f36])).

fof(f36,plain,(
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

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f77,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | r2_hidden(k4_tarski(sK3,sK4),sK2) ),
    inference(backward_demodulation,[],[f47,f71])).

fof(f71,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f44,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ! [X4] :
          ( ~ r2_hidden(k4_tarski(sK3,X4),sK2)
          | ~ m1_subset_1(X4,sK1) )
      | ~ r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) )
    & ( ( r2_hidden(k4_tarski(sK3,sK4),sK2)
        & m1_subset_1(sK4,sK1) )
      | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) )
    & m1_subset_1(sK3,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f28,f31,f30,f29])).

fof(f29,plain,
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

fof(f30,plain,
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

fof(f31,plain,
    ( ? [X5] :
        ( r2_hidden(k4_tarski(sK3,X5),sK2)
        & m1_subset_1(X5,sK1) )
   => ( r2_hidden(k4_tarski(sK3,sK4),sK2)
      & m1_subset_1(sK4,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
          <~> ? [X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
                & m1_subset_1(X4,X1) ) )
          & m1_subset_1(X3,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ! [X3] :
            ( m1_subset_1(X3,X0)
           => ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
            <=> ? [X4] :
                  ( r2_hidden(k4_tarski(X3,X4),X2)
                  & m1_subset_1(X4,X1) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f47,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),sK2)
    | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f140,plain,(
    ~ r2_hidden(sK3,k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f137,f111])).

fof(f111,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) ),
    inference(superposition,[],[f92,f98])).

fof(f98,plain,(
    sK2 = k5_relat_1(sK2,k6_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f72,f93,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f93,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f72,f70,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f70,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f44,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f72,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f44,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f92,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,X0) ),
    inference(forward_demodulation,[],[f81,f50])).

fof(f50,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f81,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f49,f72,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f49,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f137,plain,(
    ~ r2_hidden(sK3,k10_relat_1(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f135,f125])).

fof(f125,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK8(sK3,X0,sK2),sK1)
      | ~ r2_hidden(sK3,k10_relat_1(sK2,X0)) ) ),
    inference(resolution,[],[f89,f80])).

fof(f80,plain,(
    ! [X4] :
      ( ~ r2_hidden(k4_tarski(sK3,X4),sK2)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(subsumption_resolution,[],[f78,f79])).

fof(f78,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK3,k1_relat_1(sK2))
      | ~ r2_hidden(k4_tarski(sK3,X4),sK2)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(backward_demodulation,[],[f48,f71])).

fof(f48,plain,(
    ! [X4] :
      ( ~ r2_hidden(k4_tarski(sK3,X4),sK2)
      | ~ m1_subset_1(X4,sK1)
      | ~ r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f89,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(X4,sK8(X4,X5,sK2)),sK2)
      | ~ r2_hidden(X4,k10_relat_1(sK2,X5)) ) ),
    inference(resolution,[],[f72,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK8(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2)
            & r2_hidden(sK8(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK8(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2)
        & r2_hidden(sK8(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f135,plain,(
    m1_subset_1(sK8(sK3,sK1,sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f134,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f134,plain,(
    r2_hidden(sK8(sK3,sK1,sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f79,f124])).

fof(f124,plain,(
    ! [X1] :
      ( r2_hidden(sK8(X1,sK1,sK2),sK1)
      | ~ r2_hidden(X1,k1_relat_1(sK2)) ) ),
    inference(superposition,[],[f90,f111])).

fof(f90,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,k10_relat_1(sK2,X7))
      | r2_hidden(sK8(X6,X7,sK2),X7) ) ),
    inference(resolution,[],[f72,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK8(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:29:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.40  % (4431)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.41  % (4431)Refutation not found, incomplete strategy% (4431)------------------------------
% 0.20/0.41  % (4431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (4431)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.41  
% 0.20/0.41  % (4431)Memory used [KB]: 1663
% 0.20/0.41  % (4431)Time elapsed: 0.004 s
% 0.20/0.41  % (4431)------------------------------
% 0.20/0.41  % (4431)------------------------------
% 0.20/0.45  % (4433)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.45  % (4416)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.45  % (4433)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f141,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(subsumption_resolution,[],[f140,f79])).
% 0.20/0.45  fof(f79,plain,(
% 0.20/0.45    r2_hidden(sK3,k1_relat_1(sK2))),
% 0.20/0.45    inference(subsumption_resolution,[],[f77,f68])).
% 0.20/0.45  fof(f68,plain,(
% 0.20/0.45    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 0.20/0.45    inference(equality_resolution,[],[f58])).
% 0.20/0.45  fof(f58,plain,(
% 0.20/0.45    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.20/0.45    inference(cnf_transformation,[],[f39])).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f35,f38,f37,f36])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f38,plain,(
% 0.20/0.45    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.45    inference(rectify,[],[f34])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.45    inference(nnf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.20/0.45  fof(f77,plain,(
% 0.20/0.45    r2_hidden(sK3,k1_relat_1(sK2)) | r2_hidden(k4_tarski(sK3,sK4),sK2)),
% 0.20/0.45    inference(backward_demodulation,[],[f47,f71])).
% 0.20/0.45  fof(f71,plain,(
% 0.20/0.45    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f44,f66])).
% 0.20/0.45  fof(f66,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f24])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.45    inference(ennf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.45  fof(f44,plain,(
% 0.20/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.45    inference(cnf_transformation,[],[f32])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ((! [X4] : (~r2_hidden(k4_tarski(sK3,X4),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))) & ((r2_hidden(k4_tarski(sK3,sK4),sK2) & m1_subset_1(sK4,sK1)) | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))) & m1_subset_1(sK3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f28,f31,f30,f29])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k1_relset_1(X0,X1,X2))) & (? [X5] : (r2_hidden(k4_tarski(X3,X5),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k1_relset_1(X0,X1,X2))) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(X3,k1_relset_1(sK0,sK1,sK2))) & (? [X5] : (r2_hidden(k4_tarski(X3,X5),sK2) & m1_subset_1(X5,sK1)) | r2_hidden(X3,k1_relset_1(sK0,sK1,sK2))) & m1_subset_1(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    ? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(X3,k1_relset_1(sK0,sK1,sK2))) & (? [X5] : (r2_hidden(k4_tarski(X3,X5),sK2) & m1_subset_1(X5,sK1)) | r2_hidden(X3,k1_relset_1(sK0,sK1,sK2))) & m1_subset_1(X3,sK0)) => ((! [X4] : (~r2_hidden(k4_tarski(sK3,X4),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))) & (? [X5] : (r2_hidden(k4_tarski(sK3,X5),sK2) & m1_subset_1(X5,sK1)) | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))) & m1_subset_1(sK3,sK0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    ? [X5] : (r2_hidden(k4_tarski(sK3,X5),sK2) & m1_subset_1(X5,sK1)) => (r2_hidden(k4_tarski(sK3,sK4),sK2) & m1_subset_1(sK4,sK1))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k1_relset_1(X0,X1,X2))) & (? [X5] : (r2_hidden(k4_tarski(X3,X5),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k1_relset_1(X0,X1,X2))) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.45    inference(rectify,[],[f27])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k1_relset_1(X0,X1,X2))) & (? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)) | r2_hidden(X3,k1_relset_1(X0,X1,X2))) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.45    inference(flattening,[],[f26])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ? [X0,X1,X2] : (? [X3] : (((! [X4] : (~r2_hidden(k4_tarski(X3,X4),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k1_relset_1(X0,X1,X2))) & (? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)) | r2_hidden(X3,k1_relset_1(X0,X1,X2)))) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.45    inference(nnf_transformation,[],[f16])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ? [X0,X1,X2] : (? [X3] : ((r2_hidden(X3,k1_relset_1(X0,X1,X2)) <~> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1))) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.45    inference(ennf_transformation,[],[f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,k1_relset_1(X0,X1,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)))))),
% 0.20/0.45    inference(pure_predicate_removal,[],[f13])).
% 0.20/0.45  fof(f13,negated_conjecture,(
% 0.20/0.45    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,k1_relset_1(X0,X1,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)))))))),
% 0.20/0.45    inference(negated_conjecture,[],[f12])).
% 0.20/0.45  fof(f12,conjecture,(
% 0.20/0.45    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,k1_relset_1(X0,X1,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)))))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relset_1)).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    r2_hidden(k4_tarski(sK3,sK4),sK2) | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))),
% 0.20/0.45    inference(cnf_transformation,[],[f32])).
% 0.20/0.45  fof(f140,plain,(
% 0.20/0.45    ~r2_hidden(sK3,k1_relat_1(sK2))),
% 0.20/0.45    inference(forward_demodulation,[],[f137,f111])).
% 0.20/0.45  fof(f111,plain,(
% 0.20/0.45    k1_relat_1(sK2) = k10_relat_1(sK2,sK1)),
% 0.20/0.45    inference(superposition,[],[f92,f98])).
% 0.20/0.45  fof(f98,plain,(
% 0.20/0.45    sK2 = k5_relat_1(sK2,k6_relat_1(sK1))),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f72,f93,f53])).
% 0.20/0.45  fof(f53,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 0.20/0.45    inference(cnf_transformation,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.45    inference(flattening,[],[f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,axiom,(
% 0.20/0.45    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.20/0.45  fof(f93,plain,(
% 0.20/0.45    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f72,f70,f54])).
% 0.20/0.45  fof(f54,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f33])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.45    inference(nnf_transformation,[],[f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.45  fof(f70,plain,(
% 0.20/0.45    v5_relat_1(sK2,sK1)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f44,f67])).
% 0.20/0.45  fof(f67,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f25])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.45    inference(ennf_transformation,[],[f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.20/0.45    inference(pure_predicate_removal,[],[f10])).
% 0.20/0.45  fof(f10,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.45  fof(f72,plain,(
% 0.20/0.45    v1_relat_1(sK2)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f44,f65])).
% 0.20/0.45  fof(f65,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f23])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.45    inference(ennf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.45  fof(f92,plain,(
% 0.20/0.45    ( ! [X0] : (k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,X0)) )),
% 0.20/0.45    inference(forward_demodulation,[],[f81,f50])).
% 0.20/0.45  fof(f50,plain,(
% 0.20/0.45    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,axiom,(
% 0.20/0.45    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.45  fof(f81,plain,(
% 0.20/0.45    ( ! [X0] : (k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0)))) )),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f49,f72,f52])).
% 0.20/0.45  fof(f52,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.45  fof(f137,plain,(
% 0.20/0.45    ~r2_hidden(sK3,k10_relat_1(sK2,sK1))),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f135,f125])).
% 0.20/0.45  fof(f125,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_subset_1(sK8(sK3,X0,sK2),sK1) | ~r2_hidden(sK3,k10_relat_1(sK2,X0))) )),
% 0.20/0.45    inference(resolution,[],[f89,f80])).
% 0.20/0.45  fof(f80,plain,(
% 0.20/0.45    ( ! [X4] : (~r2_hidden(k4_tarski(sK3,X4),sK2) | ~m1_subset_1(X4,sK1)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f78,f79])).
% 0.20/0.45  fof(f78,plain,(
% 0.20/0.45    ( ! [X4] : (~r2_hidden(sK3,k1_relat_1(sK2)) | ~r2_hidden(k4_tarski(sK3,X4),sK2) | ~m1_subset_1(X4,sK1)) )),
% 0.20/0.45    inference(backward_demodulation,[],[f48,f71])).
% 0.20/0.45  fof(f48,plain,(
% 0.20/0.45    ( ! [X4] : (~r2_hidden(k4_tarski(sK3,X4),sK2) | ~m1_subset_1(X4,sK1) | ~r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f32])).
% 0.20/0.45  fof(f89,plain,(
% 0.20/0.45    ( ! [X4,X5] : (r2_hidden(k4_tarski(X4,sK8(X4,X5,sK2)),sK2) | ~r2_hidden(X4,k10_relat_1(sK2,X5))) )),
% 0.20/0.45    inference(resolution,[],[f72,f62])).
% 0.20/0.45  fof(f62,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f43])).
% 0.20/0.45  fof(f43,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2) & r2_hidden(sK8(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f41,f42])).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2) & r2_hidden(sK8(X0,X1,X2),k2_relat_1(X2))))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.45    inference(rectify,[],[f40])).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.45    inference(nnf_transformation,[],[f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.20/0.45    inference(ennf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 0.20/0.45  fof(f135,plain,(
% 0.20/0.45    m1_subset_1(sK8(sK3,sK1,sK2),sK1)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f134,f56])).
% 0.20/0.45  fof(f56,plain,(
% 0.20/0.45    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f21])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.45  fof(f134,plain,(
% 0.20/0.45    r2_hidden(sK8(sK3,sK1,sK2),sK1)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f79,f124])).
% 0.20/0.45  fof(f124,plain,(
% 0.20/0.45    ( ! [X1] : (r2_hidden(sK8(X1,sK1,sK2),sK1) | ~r2_hidden(X1,k1_relat_1(sK2))) )),
% 0.20/0.45    inference(superposition,[],[f90,f111])).
% 0.20/0.45  fof(f90,plain,(
% 0.20/0.45    ( ! [X6,X7] : (~r2_hidden(X6,k10_relat_1(sK2,X7)) | r2_hidden(sK8(X6,X7,sK2),X7)) )),
% 0.20/0.45    inference(resolution,[],[f72,f63])).
% 0.20/0.45  fof(f63,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK8(X0,X1,X2),X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f43])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (4433)------------------------------
% 0.20/0.45  % (4433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (4433)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (4433)Memory used [KB]: 6268
% 0.20/0.45  % (4433)Time elapsed: 0.037 s
% 0.20/0.45  % (4433)------------------------------
% 0.20/0.45  % (4433)------------------------------
% 0.20/0.45  % (4415)Success in time 0.101 s
%------------------------------------------------------------------------------
