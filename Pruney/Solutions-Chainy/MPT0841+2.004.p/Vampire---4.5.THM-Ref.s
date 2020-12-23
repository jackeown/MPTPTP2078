%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 567 expanded)
%              Number of leaves         :   15 ( 163 expanded)
%              Depth                    :   25
%              Number of atoms          :  437 (4201 expanded)
%              Number of equality atoms :   12 (  33 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f177,plain,(
    $false ),
    inference(subsumption_resolution,[],[f176,f119])).

fof(f119,plain,(
    m1_subset_1(sK5,sK2) ),
    inference(subsumption_resolution,[],[f118,f104])).

fof(f104,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | m1_subset_1(sK5,sK2) ),
    inference(subsumption_resolution,[],[f103,f68])).

fof(f68,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f55,f37])).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ! [X5] :
          ( ~ r2_hidden(X5,sK1)
          | ~ r2_hidden(k4_tarski(X5,sK4),sK3)
          | ~ m1_subset_1(X5,sK2) )
      | ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) )
    & ( ( r2_hidden(sK5,sK1)
        & r2_hidden(k4_tarski(sK5,sK4),sK3)
        & m1_subset_1(sK5,sK2) )
      | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) )
    & m1_subset_1(sK4,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f20,f23,f22,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ( ! [X5] :
                  ( ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(k4_tarski(X5,X4),X3)
                  | ~ m1_subset_1(X5,X2) )
              | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
            & ( ? [X6] :
                  ( r2_hidden(X6,X1)
                  & r2_hidden(k4_tarski(X6,X4),X3)
                  & m1_subset_1(X6,X2) )
              | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
            & m1_subset_1(X4,X0) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,sK1)
                | ~ r2_hidden(k4_tarski(X5,X4),sK3)
                | ~ m1_subset_1(X5,sK2) )
            | ~ r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1)) )
          & ( ? [X6] :
                ( r2_hidden(X6,sK1)
                & r2_hidden(k4_tarski(X6,X4),sK3)
                & m1_subset_1(X6,sK2) )
            | r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1)) )
          & m1_subset_1(X4,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X4] :
        ( ( ! [X5] :
              ( ~ r2_hidden(X5,sK1)
              | ~ r2_hidden(k4_tarski(X5,X4),sK3)
              | ~ m1_subset_1(X5,sK2) )
          | ~ r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1)) )
        & ( ? [X6] :
              ( r2_hidden(X6,sK1)
              & r2_hidden(k4_tarski(X6,X4),sK3)
              & m1_subset_1(X6,sK2) )
          | r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1)) )
        & m1_subset_1(X4,sK0) )
   => ( ( ! [X5] :
            ( ~ r2_hidden(X5,sK1)
            | ~ r2_hidden(k4_tarski(X5,sK4),sK3)
            | ~ m1_subset_1(X5,sK2) )
        | ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) )
      & ( ? [X6] :
            ( r2_hidden(X6,sK1)
            & r2_hidden(k4_tarski(X6,sK4),sK3)
            & m1_subset_1(X6,sK2) )
        | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) )
      & m1_subset_1(sK4,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X6] :
        ( r2_hidden(X6,sK1)
        & r2_hidden(k4_tarski(X6,sK4),sK3)
        & m1_subset_1(X6,sK2) )
   => ( r2_hidden(sK5,sK1)
      & r2_hidden(k4_tarski(sK5,sK4),sK3)
      & m1_subset_1(sK5,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,X1)
                | ~ r2_hidden(k4_tarski(X5,X4),X3)
                | ~ m1_subset_1(X5,X2) )
            | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & ( ? [X6] :
                ( r2_hidden(X6,X1)
                & r2_hidden(k4_tarski(X6,X4),X3)
                & m1_subset_1(X6,X2) )
            | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,X1)
                | ~ r2_hidden(k4_tarski(X5,X4),X3)
                | ~ m1_subset_1(X5,X2) )
            | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X4),X3)
                & m1_subset_1(X5,X2) )
            | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,X1)
                | ~ r2_hidden(k4_tarski(X5,X4),X3)
                | ~ m1_subset_1(X5,X2) )
            | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X4),X3)
                & m1_subset_1(X5,X2) )
            | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
          <~> ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X4),X3)
                & m1_subset_1(X5,X2) ) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => ! [X4] :
            ( m1_subset_1(X4,X0)
           => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
            <=> ? [X5] :
                  ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X5,X4),X3)
                  & m1_subset_1(X5,X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                        <=> ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X5,X4),X3)
                              & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f103,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | m1_subset_1(sK5,sK2)
    | ~ v1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | m1_subset_1(sK5,sK2)
    | ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f101,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK9(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2)
            & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK9(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2)
        & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f101,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK9(sK4,X0,sK3),sK1)
      | ~ r2_hidden(sK4,k9_relat_1(sK3,X0))
      | m1_subset_1(sK5,sK2) ) ),
    inference(subsumption_resolution,[],[f100,f96])).

fof(f96,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK9(X5,X6,sK3),sK2)
      | ~ r2_hidden(X5,k9_relat_1(sK3,X6)) ) ),
    inference(subsumption_resolution,[],[f87,f68])).

fof(f87,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,k9_relat_1(sK3,X6))
      | ~ v1_relat_1(sK3)
      | r2_hidden(sK9(X5,X6,sK3),sK2) ) ),
    inference(resolution,[],[f52,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
      | r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f57,f70])).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK2,sK0))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f50,f37])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f100,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,k9_relat_1(sK3,X0))
      | ~ r2_hidden(sK9(sK4,X0,sK3),sK1)
      | m1_subset_1(sK5,sK2)
      | ~ r2_hidden(sK9(sK4,X0,sK3),sK2) ) ),
    inference(resolution,[],[f93,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    ! [X1] :
      ( ~ m1_subset_1(sK9(sK4,X1,sK3),sK2)
      | ~ r2_hidden(sK4,k9_relat_1(sK3,X1))
      | ~ r2_hidden(sK9(sK4,X1,sK3),sK1)
      | m1_subset_1(sK5,sK2) ) ),
    inference(subsumption_resolution,[],[f84,f68])).

fof(f84,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4,k9_relat_1(sK3,X1))
      | ~ v1_relat_1(sK3)
      | ~ m1_subset_1(sK9(sK4,X1,sK3),sK2)
      | ~ r2_hidden(sK9(sK4,X1,sK3),sK1)
      | m1_subset_1(sK5,sK2) ) ),
    inference(resolution,[],[f52,f65])).

fof(f65,plain,(
    ! [X2] :
      ( ~ r2_hidden(k4_tarski(X2,sK4),sK3)
      | ~ m1_subset_1(X2,sK2)
      | ~ r2_hidden(X2,sK1)
      | m1_subset_1(sK5,sK2) ) ),
    inference(resolution,[],[f42,f39])).

fof(f39,plain,
    ( r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
    | m1_subset_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X5] :
      ( ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
      | ~ r2_hidden(k4_tarski(X5,sK4),sK3)
      | ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f118,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | m1_subset_1(sK5,sK2) ),
    inference(subsumption_resolution,[],[f113,f37])).

fof(f113,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | m1_subset_1(sK5,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(superposition,[],[f39,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f176,plain,(
    ~ m1_subset_1(sK5,sK2) ),
    inference(subsumption_resolution,[],[f170,f117])).

fof(f117,plain,(
    r2_hidden(sK5,sK1) ),
    inference(subsumption_resolution,[],[f116,f109])).

fof(f109,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | r2_hidden(sK5,sK1) ),
    inference(subsumption_resolution,[],[f108,f68])).

fof(f108,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | r2_hidden(sK5,sK1)
    | ~ v1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | r2_hidden(sK5,sK1)
    | ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f106,f53])).

fof(f106,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK9(sK4,X0,sK3),sK1)
      | ~ r2_hidden(sK4,k9_relat_1(sK3,X0))
      | r2_hidden(sK5,sK1) ) ),
    inference(subsumption_resolution,[],[f105,f96])).

fof(f105,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,k9_relat_1(sK3,X0))
      | ~ r2_hidden(sK9(sK4,X0,sK3),sK1)
      | r2_hidden(sK5,sK1)
      | ~ r2_hidden(sK9(sK4,X0,sK3),sK2) ) ),
    inference(resolution,[],[f94,f49])).

fof(f94,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK9(sK4,X2,sK3),sK2)
      | ~ r2_hidden(sK4,k9_relat_1(sK3,X2))
      | ~ r2_hidden(sK9(sK4,X2,sK3),sK1)
      | r2_hidden(sK5,sK1) ) ),
    inference(subsumption_resolution,[],[f85,f68])).

fof(f85,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK4,k9_relat_1(sK3,X2))
      | ~ v1_relat_1(sK3)
      | ~ m1_subset_1(sK9(sK4,X2,sK3),sK2)
      | ~ r2_hidden(sK9(sK4,X2,sK3),sK1)
      | r2_hidden(sK5,sK1) ) ),
    inference(resolution,[],[f52,f64])).

fof(f64,plain,(
    ! [X1] :
      ( ~ r2_hidden(k4_tarski(X1,sK4),sK3)
      | ~ m1_subset_1(X1,sK2)
      | ~ r2_hidden(X1,sK1)
      | r2_hidden(sK5,sK1) ) ),
    inference(resolution,[],[f42,f41])).

fof(f41,plain,
    ( r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
    | r2_hidden(sK5,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f116,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | r2_hidden(sK5,sK1) ),
    inference(subsumption_resolution,[],[f112,f37])).

fof(f112,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | r2_hidden(sK5,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(superposition,[],[f41,f56])).

fof(f170,plain,
    ( ~ r2_hidden(sK5,sK1)
    | ~ m1_subset_1(sK5,sK2) ),
    inference(resolution,[],[f167,f144])).

fof(f144,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK4),sK3)
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f142,f68])).

fof(f142,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(k4_tarski(X0,sK4),sK3)
      | ~ v1_relat_1(sK3)
      | ~ m1_subset_1(X0,sK2) ) ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(k4_tarski(X0,sK4),sK3)
      | ~ v1_relat_1(sK3)
      | ~ r2_hidden(k4_tarski(X0,sK4),sK3)
      | ~ m1_subset_1(X0,sK2) ) ),
    inference(condensation,[],[f138])).

fof(f138,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(X9,sK1)
      | ~ r2_hidden(k4_tarski(X9,sK4),sK3)
      | ~ v1_relat_1(sK3)
      | ~ r2_hidden(k4_tarski(X10,sK4),sK3)
      | ~ m1_subset_1(X10,sK2)
      | ~ r2_hidden(X10,sK1) ) ),
    inference(resolution,[],[f60,f114])).

fof(f114,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
      | ~ r2_hidden(k4_tarski(X0,sK4),sK3)
      | ~ m1_subset_1(X0,sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f110,f37])).

fof(f110,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
      | ~ r2_hidden(k4_tarski(X0,sK4),sK3)
      | ~ m1_subset_1(X0,sK2)
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ) ),
    inference(superposition,[],[f42,f56])).

fof(f60,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK6(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK6(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK7(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X0) )
                | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK8(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK8(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f26,f29,f28,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X4,X3),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X3),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X4,sK6(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X0) )
     => ( r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK8(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK8(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X5,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X8,X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

fof(f167,plain,(
    r2_hidden(k4_tarski(sK5,sK4),sK3) ),
    inference(resolution,[],[f152,f115])).

fof(f115,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | r2_hidden(k4_tarski(sK5,sK4),sK3) ),
    inference(subsumption_resolution,[],[f111,f37])).

fof(f111,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(superposition,[],[f40,f56])).

fof(f40,plain,
    ( r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
    | r2_hidden(k4_tarski(sK5,sK4),sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f152,plain,(
    ~ r2_hidden(sK4,k9_relat_1(sK3,sK1)) ),
    inference(subsumption_resolution,[],[f151,f68])).

fof(f151,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f150])).

fof(f150,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f149,f53])).

fof(f149,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK9(sK4,X0,sK3),sK1)
      | ~ r2_hidden(sK4,k9_relat_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f148,f96])).

fof(f148,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK9(sK4,X0,sK3),sK1)
      | ~ r2_hidden(sK4,k9_relat_1(sK3,X0))
      | ~ r2_hidden(sK9(sK4,X0,sK3),sK2) ) ),
    inference(resolution,[],[f147,f49])).

fof(f147,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK9(sK4,X1,sK3),sK2)
      | ~ r2_hidden(sK9(sK4,X1,sK3),sK1)
      | ~ r2_hidden(sK4,k9_relat_1(sK3,X1)) ) ),
    inference(subsumption_resolution,[],[f146,f68])).

fof(f146,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK9(sK4,X1,sK3),sK1)
      | ~ m1_subset_1(sK9(sK4,X1,sK3),sK2)
      | ~ r2_hidden(sK4,k9_relat_1(sK3,X1))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f144,f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:59:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (3009)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (2999)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (3014)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.48  % (3006)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (3010)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (3014)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f176,f119])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    m1_subset_1(sK5,sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f118,f104])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | m1_subset_1(sK5,sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f103,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    v1_relat_1(sK3)),
% 0.21/0.48    inference(resolution,[],[f55,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X5,sK4),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))) & ((r2_hidden(sK5,sK1) & r2_hidden(k4_tarski(sK5,sK4),sK3) & m1_subset_1(sK5,sK2)) | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))) & m1_subset_1(sK4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f20,f23,f22,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) => (? [X4] : ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X5,X4),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1))) & (? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(X6,X4),sK3) & m1_subset_1(X6,sK2)) | r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1))) & m1_subset_1(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ? [X4] : ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X5,X4),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1))) & (? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(X6,X4),sK3) & m1_subset_1(X6,sK2)) | r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1))) & m1_subset_1(X4,sK0)) => ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X5,sK4),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))) & (? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(X6,sK4),sK3) & m1_subset_1(X6,sK2)) | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))) & m1_subset_1(sK4,sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(X6,sK4),sK3) & m1_subset_1(X6,sK2)) => (r2_hidden(sK5,sK1) & r2_hidden(k4_tarski(sK5,sK4),sK3) & m1_subset_1(sK5,sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.48    inference(rectify,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (? [X4] : (((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.48    inference(nnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (? [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)))))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.48  fof(f9,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f8])).
% 0.21/0.48  fof(f8,conjecture,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | m1_subset_1(sK5,sK2) | ~v1_relat_1(sK3)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f102])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | m1_subset_1(sK5,sK2) | ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~v1_relat_1(sK3)),
% 0.21/0.48    inference(resolution,[],[f101,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2) & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f32,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2) & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X2))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(rectify,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(nnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(sK9(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k9_relat_1(sK3,X0)) | m1_subset_1(sK5,sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f100,f96])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ( ! [X6,X5] : (r2_hidden(sK9(X5,X6,sK3),sK2) | ~r2_hidden(X5,k9_relat_1(sK3,X6))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f87,f68])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ( ! [X6,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X6)) | ~v1_relat_1(sK3) | r2_hidden(sK9(X5,X6,sK3),sK2)) )),
% 0.21/0.48    inference(resolution,[],[f52,f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK3) | r2_hidden(X0,sK2)) )),
% 0.21/0.48    inference(resolution,[],[f57,f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK2,sK0)) | ~r2_hidden(X0,sK3)) )),
% 0.21/0.48    inference(resolution,[],[f50,f37])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.48    inference(flattening,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.48    inference(nnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(sK4,k9_relat_1(sK3,X0)) | ~r2_hidden(sK9(sK4,X0,sK3),sK1) | m1_subset_1(sK5,sK2) | ~r2_hidden(sK9(sK4,X0,sK3),sK2)) )),
% 0.21/0.48    inference(resolution,[],[f93,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ( ! [X1] : (~m1_subset_1(sK9(sK4,X1,sK3),sK2) | ~r2_hidden(sK4,k9_relat_1(sK3,X1)) | ~r2_hidden(sK9(sK4,X1,sK3),sK1) | m1_subset_1(sK5,sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f84,f68])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ( ! [X1] : (~r2_hidden(sK4,k9_relat_1(sK3,X1)) | ~v1_relat_1(sK3) | ~m1_subset_1(sK9(sK4,X1,sK3),sK2) | ~r2_hidden(sK9(sK4,X1,sK3),sK1) | m1_subset_1(sK5,sK2)) )),
% 0.21/0.48    inference(resolution,[],[f52,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X2] : (~r2_hidden(k4_tarski(X2,sK4),sK3) | ~m1_subset_1(X2,sK2) | ~r2_hidden(X2,sK1) | m1_subset_1(sK5,sK2)) )),
% 0.21/0.48    inference(resolution,[],[f42,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) | m1_subset_1(sK5,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X5] : (~r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) | ~r2_hidden(k4_tarski(X5,sK4),sK3) | ~m1_subset_1(X5,sK2) | ~r2_hidden(X5,sK1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | m1_subset_1(sK5,sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f113,f37])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | m1_subset_1(sK5,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.48    inference(superposition,[],[f39,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    ~m1_subset_1(sK5,sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f170,f117])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    r2_hidden(sK5,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f116,f109])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | r2_hidden(sK5,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f108,f68])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | r2_hidden(sK5,sK1) | ~v1_relat_1(sK3)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f107])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | r2_hidden(sK5,sK1) | ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~v1_relat_1(sK3)),
% 0.21/0.48    inference(resolution,[],[f106,f53])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(sK9(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k9_relat_1(sK3,X0)) | r2_hidden(sK5,sK1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f105,f96])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(sK4,k9_relat_1(sK3,X0)) | ~r2_hidden(sK9(sK4,X0,sK3),sK1) | r2_hidden(sK5,sK1) | ~r2_hidden(sK9(sK4,X0,sK3),sK2)) )),
% 0.21/0.48    inference(resolution,[],[f94,f49])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    ( ! [X2] : (~m1_subset_1(sK9(sK4,X2,sK3),sK2) | ~r2_hidden(sK4,k9_relat_1(sK3,X2)) | ~r2_hidden(sK9(sK4,X2,sK3),sK1) | r2_hidden(sK5,sK1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f85,f68])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X2] : (~r2_hidden(sK4,k9_relat_1(sK3,X2)) | ~v1_relat_1(sK3) | ~m1_subset_1(sK9(sK4,X2,sK3),sK2) | ~r2_hidden(sK9(sK4,X2,sK3),sK1) | r2_hidden(sK5,sK1)) )),
% 0.21/0.48    inference(resolution,[],[f52,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X1] : (~r2_hidden(k4_tarski(X1,sK4),sK3) | ~m1_subset_1(X1,sK2) | ~r2_hidden(X1,sK1) | r2_hidden(sK5,sK1)) )),
% 0.21/0.48    inference(resolution,[],[f42,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) | r2_hidden(sK5,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | r2_hidden(sK5,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f112,f37])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | r2_hidden(sK5,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.48    inference(superposition,[],[f41,f56])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    ~r2_hidden(sK5,sK1) | ~m1_subset_1(sK5,sK2)),
% 0.21/0.48    inference(resolution,[],[f167,f144])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK4),sK3) | ~r2_hidden(X0,sK1) | ~m1_subset_1(X0,sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f142,f68])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(k4_tarski(X0,sK4),sK3) | ~v1_relat_1(sK3) | ~m1_subset_1(X0,sK2)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f141])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(k4_tarski(X0,sK4),sK3) | ~v1_relat_1(sK3) | ~r2_hidden(k4_tarski(X0,sK4),sK3) | ~m1_subset_1(X0,sK2)) )),
% 0.21/0.48    inference(condensation,[],[f138])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    ( ! [X10,X9] : (~r2_hidden(X9,sK1) | ~r2_hidden(k4_tarski(X9,sK4),sK3) | ~v1_relat_1(sK3) | ~r2_hidden(k4_tarski(X10,sK4),sK3) | ~m1_subset_1(X10,sK2) | ~r2_hidden(X10,sK1)) )),
% 0.21/0.48    inference(resolution,[],[f60,f114])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~r2_hidden(k4_tarski(X0,sK4),sK3) | ~m1_subset_1(X0,sK2) | ~r2_hidden(X0,sK1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f110,f37])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~r2_hidden(k4_tarski(X0,sK4),sK3) | ~m1_subset_1(X0,sK2) | ~r2_hidden(X0,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))) )),
% 0.21/0.48    inference(superposition,[],[f42,f56])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k9_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK6(X0,X1,X2)),X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X0)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & ((r2_hidden(sK8(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X6),X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f26,f29,f28,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK6(X0,X1,X2)),X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X0)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X0)) => (r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) => (r2_hidden(sK8(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X6),X6),X0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(rectify,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK5,sK4),sK3)),
% 0.21/0.48    inference(resolution,[],[f152,f115])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | r2_hidden(k4_tarski(sK5,sK4),sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f111,f37])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | r2_hidden(k4_tarski(sK5,sK4),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.48    inference(superposition,[],[f40,f56])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) | r2_hidden(k4_tarski(sK5,sK4),sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    ~r2_hidden(sK4,k9_relat_1(sK3,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f151,f68])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~v1_relat_1(sK3)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f150])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~v1_relat_1(sK3)),
% 0.21/0.48    inference(resolution,[],[f149,f53])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(sK9(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k9_relat_1(sK3,X0))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f148,f96])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(sK9(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k9_relat_1(sK3,X0)) | ~r2_hidden(sK9(sK4,X0,sK3),sK2)) )),
% 0.21/0.48    inference(resolution,[],[f147,f49])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    ( ! [X1] : (~m1_subset_1(sK9(sK4,X1,sK3),sK2) | ~r2_hidden(sK9(sK4,X1,sK3),sK1) | ~r2_hidden(sK4,k9_relat_1(sK3,X1))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f146,f68])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    ( ! [X1] : (~r2_hidden(sK9(sK4,X1,sK3),sK1) | ~m1_subset_1(sK9(sK4,X1,sK3),sK2) | ~r2_hidden(sK4,k9_relat_1(sK3,X1)) | ~v1_relat_1(sK3)) )),
% 0.21/0.48    inference(resolution,[],[f144,f52])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (3014)------------------------------
% 0.21/0.48  % (3014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (3014)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (3014)Memory used [KB]: 1791
% 0.21/0.48  % (3014)Time elapsed: 0.080 s
% 0.21/0.48  % (3014)------------------------------
% 0.21/0.48  % (3014)------------------------------
% 0.21/0.48  % (3002)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (2990)Success in time 0.121 s
%------------------------------------------------------------------------------
