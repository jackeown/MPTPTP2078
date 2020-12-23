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
% DateTime   : Thu Dec  3 12:58:00 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 555 expanded)
%              Number of leaves         :   13 ( 162 expanded)
%              Depth                    :   20
%              Number of atoms          :  306 (3894 expanded)
%              Number of equality atoms :    4 (  24 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f789,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f749,f749,f751,f161])).

fof(f161,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5,X0)
      | r2_hidden(sK4,k10_relat_1(sK3,X0))
      | r2_hidden(sK4,k10_relat_1(sK3,sK1)) ) ),
    inference(subsumption_resolution,[],[f120,f119])).

fof(f119,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | r2_hidden(sK5,k2_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f110,f54])).

fof(f54,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f52,f33,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ! [X5] :
          ( ~ r2_hidden(X5,sK1)
          | ~ r2_hidden(k4_tarski(sK4,X5),sK3)
          | ~ m1_subset_1(X5,sK2) )
      | ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) )
    & ( ( r2_hidden(sK5,sK1)
        & r2_hidden(k4_tarski(sK4,sK5),sK3)
        & m1_subset_1(sK5,sK2) )
      | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) )
    & m1_subset_1(sK4,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f22,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ( ! [X5] :
                  ( ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(k4_tarski(X4,X5),X3)
                  | ~ m1_subset_1(X5,X2) )
              | ~ r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
            & ( ? [X6] :
                  ( r2_hidden(X6,X1)
                  & r2_hidden(k4_tarski(X4,X6),X3)
                  & m1_subset_1(X6,X2) )
              | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
            & m1_subset_1(X4,X0) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
   => ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,sK1)
                | ~ r2_hidden(k4_tarski(X4,X5),sK3)
                | ~ m1_subset_1(X5,sK2) )
            | ~ r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1)) )
          & ( ? [X6] :
                ( r2_hidden(X6,sK1)
                & r2_hidden(k4_tarski(X4,X6),sK3)
                & m1_subset_1(X6,sK2) )
            | r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1)) )
          & m1_subset_1(X4,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X4] :
        ( ( ! [X5] :
              ( ~ r2_hidden(X5,sK1)
              | ~ r2_hidden(k4_tarski(X4,X5),sK3)
              | ~ m1_subset_1(X5,sK2) )
          | ~ r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1)) )
        & ( ? [X6] :
              ( r2_hidden(X6,sK1)
              & r2_hidden(k4_tarski(X4,X6),sK3)
              & m1_subset_1(X6,sK2) )
          | r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1)) )
        & m1_subset_1(X4,sK0) )
   => ( ( ! [X5] :
            ( ~ r2_hidden(X5,sK1)
            | ~ r2_hidden(k4_tarski(sK4,X5),sK3)
            | ~ m1_subset_1(X5,sK2) )
        | ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) )
      & ( ? [X6] :
            ( r2_hidden(X6,sK1)
            & r2_hidden(k4_tarski(sK4,X6),sK3)
            & m1_subset_1(X6,sK2) )
        | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) )
      & m1_subset_1(sK4,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X6] :
        ( r2_hidden(X6,sK1)
        & r2_hidden(k4_tarski(sK4,X6),sK3)
        & m1_subset_1(X6,sK2) )
   => ( r2_hidden(sK5,sK1)
      & r2_hidden(k4_tarski(sK4,sK5),sK3)
      & m1_subset_1(sK5,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X3)
                | ~ m1_subset_1(X5,X2) )
            | ~ r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
          & ( ? [X6] :
                ( r2_hidden(X6,X1)
                & r2_hidden(k4_tarski(X4,X6),X3)
                & m1_subset_1(X6,X2) )
            | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X3)
                | ~ m1_subset_1(X5,X2) )
            | ~ r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X4,X5),X3)
                & m1_subset_1(X5,X2) )
            | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X3)
                | ~ m1_subset_1(X5,X2) )
            | ~ r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X4,X5),X3)
                & m1_subset_1(X5,X2) )
            | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
          <~> ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X4,X5),X3)
                & m1_subset_1(X5,X2) ) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ! [X4] :
            ( m1_subset_1(X4,X0)
           => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
            <=> ? [X5] :
                  ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X4,X5),X3)
                  & m1_subset_1(X5,X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                        <=> ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X4,X5),X3)
                              & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X4,X5),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_relset_1)).

fof(f52,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f110,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | r2_hidden(sK5,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f90,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(f90,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | r2_hidden(sK4,k10_relat_1(sK3,sK1)) ),
    inference(backward_demodulation,[],[f36,f53])).

fof(f53,plain,(
    ! [X0] : k8_relset_1(sK0,sK2,sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(unit_resulting_resolution,[],[f33,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f36,plain,
    ( r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | r2_hidden(k4_tarski(sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f120,plain,(
    ! [X0] :
      ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
      | r2_hidden(sK4,k10_relat_1(sK3,X0))
      | ~ r2_hidden(sK5,X0)
      | ~ r2_hidden(sK5,k2_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f111,f54])).

fof(f111,plain,(
    ! [X0] :
      ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
      | r2_hidden(sK4,k10_relat_1(sK3,X0))
      | ~ r2_hidden(sK5,X0)
      | ~ r2_hidden(sK5,k2_relat_1(sK3))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f90,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2)
            & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2)
        & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f751,plain,(
    r2_hidden(sK5,sK1) ),
    inference(unit_resulting_resolution,[],[f749,f91])).

fof(f91,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | r2_hidden(sK5,sK1) ),
    inference(backward_demodulation,[],[f37,f53])).

fof(f37,plain,
    ( r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | r2_hidden(sK5,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f749,plain,(
    ~ r2_hidden(sK4,k10_relat_1(sK3,sK1)) ),
    inference(subsumption_resolution,[],[f748,f54])).

fof(f748,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f744])).

fof(f744,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f260,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f260,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK6(sK4,X0,sK3),sK1)
      | ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
      | ~ r2_hidden(sK4,k10_relat_1(sK3,X0)) ) ),
    inference(duplicate_literal_removal,[],[f254])).

fof(f254,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,k10_relat_1(sK3,X0))
      | ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
      | ~ r2_hidden(sK6(sK4,X0,sK3),sK1)
      | ~ r2_hidden(sK4,k10_relat_1(sK3,X0)) ) ),
    inference(resolution,[],[f210,f147])).

fof(f147,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK6(sK4,X0,sK3),sK2)
      | ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
      | ~ r2_hidden(sK6(sK4,X0,sK3),sK1)
      | ~ r2_hidden(sK4,k10_relat_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f143,f54])).

fof(f143,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK6(sK4,X0,sK3),sK1)
      | ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
      | ~ r2_hidden(sK6(sK4,X0,sK3),sK2)
      | ~ r2_hidden(sK4,k10_relat_1(sK3,X0))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f130,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f130,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK4,X0),sK3)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f121,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f121,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(k4_tarski(sK4,X5),sK3)
      | ~ r2_hidden(sK4,k10_relat_1(sK3,sK1)) ) ),
    inference(forward_demodulation,[],[f38,f53])).

fof(f38,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(k4_tarski(sK4,X5),sK3)
      | ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f210,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK6(X2,X3,sK3),sK2)
      | ~ r2_hidden(X2,k10_relat_1(sK3,X3)) ) ),
    inference(resolution,[],[f83,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f83,plain,(
    ! [X8,X9] :
      ( r2_hidden(k4_tarski(X8,sK6(X8,X9,sK3)),k2_zfmisc_1(sK0,sK2))
      | ~ r2_hidden(X8,k10_relat_1(sK3,X9)) ) ),
    inference(subsumption_resolution,[],[f81,f54])).

fof(f81,plain,(
    ! [X8,X9] :
      ( r2_hidden(k4_tarski(X8,sK6(X8,X9,sK3)),k2_zfmisc_1(sK0,sK2))
      | ~ r2_hidden(X8,k10_relat_1(sK3,X9))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f57,f43])).

fof(f57,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK3)
      | r2_hidden(X1,k2_zfmisc_1(sK0,sK2)) ) ),
    inference(resolution,[],[f33,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:22:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (26462)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.48  % (26470)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.48  % (26475)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.48  % (26467)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.50  % (26454)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.50  % (26455)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % (26461)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.51  % (26474)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.51  % (26457)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (26466)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.51  % (26456)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (26452)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.51  % (26460)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.51  % (26473)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.52  % (26458)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.52  % (26459)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (26472)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.52  % (26463)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.52  % (26465)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.53  % (26453)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.53  % (26469)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.53  % (26471)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.53  % (26464)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.54  % (26468)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.52/0.56  % (26468)Refutation not found, incomplete strategy% (26468)------------------------------
% 1.52/0.56  % (26468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (26468)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (26468)Memory used [KB]: 1663
% 1.52/0.56  % (26468)Time elapsed: 0.148 s
% 1.52/0.56  % (26468)------------------------------
% 1.52/0.56  % (26468)------------------------------
% 1.52/0.56  % (26469)Refutation found. Thanks to Tanya!
% 1.52/0.56  % SZS status Theorem for theBenchmark
% 1.52/0.56  % SZS output start Proof for theBenchmark
% 1.52/0.56  fof(f789,plain,(
% 1.52/0.56    $false),
% 1.52/0.56    inference(unit_resulting_resolution,[],[f749,f749,f751,f161])).
% 1.52/0.56  fof(f161,plain,(
% 1.52/0.56    ( ! [X0] : (~r2_hidden(sK5,X0) | r2_hidden(sK4,k10_relat_1(sK3,X0)) | r2_hidden(sK4,k10_relat_1(sK3,sK1))) )),
% 1.52/0.56    inference(subsumption_resolution,[],[f120,f119])).
% 1.52/0.56  fof(f119,plain,(
% 1.52/0.56    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | r2_hidden(sK5,k2_relat_1(sK3))),
% 1.52/0.56    inference(subsumption_resolution,[],[f110,f54])).
% 1.52/0.56  fof(f54,plain,(
% 1.52/0.56    v1_relat_1(sK3)),
% 1.52/0.56    inference(unit_resulting_resolution,[],[f52,f33,f51])).
% 1.52/0.56  fof(f51,plain,(
% 1.52/0.56    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f19])).
% 1.52/0.56  fof(f19,plain,(
% 1.52/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.52/0.56    inference(ennf_transformation,[],[f4])).
% 1.52/0.56  fof(f4,axiom,(
% 1.52/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.52/0.56  fof(f33,plain,(
% 1.52/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.52/0.56    inference(cnf_transformation,[],[f26])).
% 1.52/0.56  fof(f26,plain,(
% 1.52/0.56    ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(sK4,X5),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) & ((r2_hidden(sK5,sK1) & r2_hidden(k4_tarski(sK4,sK5),sK3) & m1_subset_1(sK5,sK2)) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) & m1_subset_1(sK4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.52/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f22,f25,f24,f23])).
% 1.52/0.56  fof(f23,plain,(
% 1.52/0.56    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) => (? [X4] : ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X4,X5),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1))) & (? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(X4,X6),sK3) & m1_subset_1(X6,sK2)) | r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1))) & m1_subset_1(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))))),
% 1.52/0.56    introduced(choice_axiom,[])).
% 1.52/0.56  fof(f24,plain,(
% 1.52/0.56    ? [X4] : ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X4,X5),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1))) & (? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(X4,X6),sK3) & m1_subset_1(X6,sK2)) | r2_hidden(X4,k8_relset_1(sK0,sK2,sK3,sK1))) & m1_subset_1(X4,sK0)) => ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(sK4,X5),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) & (? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(sK4,X6),sK3) & m1_subset_1(X6,sK2)) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) & m1_subset_1(sK4,sK0))),
% 1.52/0.56    introduced(choice_axiom,[])).
% 1.52/0.56  fof(f25,plain,(
% 1.52/0.56    ? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(sK4,X6),sK3) & m1_subset_1(X6,sK2)) => (r2_hidden(sK5,sK1) & r2_hidden(k4_tarski(sK4,sK5),sK3) & m1_subset_1(sK5,sK2))),
% 1.52/0.56    introduced(choice_axiom,[])).
% 1.52/0.56  fof(f22,plain,(
% 1.52/0.56    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X4,X6),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.52/0.56    inference(rectify,[],[f21])).
% 1.52/0.56  fof(f21,plain,(
% 1.52/0.56    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.52/0.56    inference(flattening,[],[f20])).
% 1.52/0.56  fof(f20,plain,(
% 1.52/0.56    ? [X0,X1,X2,X3] : (? [X4] : (((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X4,X5),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.52/0.56    inference(nnf_transformation,[],[f12])).
% 1.52/0.56  fof(f12,plain,(
% 1.52/0.56    ? [X0,X1,X2,X3] : (? [X4] : ((r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.52/0.56    inference(ennf_transformation,[],[f11])).
% 1.52/0.56  fof(f11,plain,(
% 1.52/0.56    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2)))))),
% 1.52/0.56    inference(pure_predicate_removal,[],[f10])).
% 1.52/0.56  fof(f10,negated_conjecture,(
% 1.52/0.56    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 1.52/0.56    inference(negated_conjecture,[],[f9])).
% 1.52/0.56  fof(f9,conjecture,(
% 1.52/0.56    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_relset_1)).
% 1.52/0.56  fof(f52,plain,(
% 1.52/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.52/0.56    inference(cnf_transformation,[],[f5])).
% 1.52/0.56  fof(f5,axiom,(
% 1.52/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.52/0.56  fof(f110,plain,(
% 1.52/0.56    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | r2_hidden(sK5,k2_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 1.52/0.56    inference(resolution,[],[f90,f47])).
% 1.52/0.56  fof(f47,plain,(
% 1.52/0.56    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f15])).
% 1.52/0.56  fof(f15,plain,(
% 1.52/0.56    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 1.52/0.56    inference(flattening,[],[f14])).
% 1.52/0.56  fof(f14,plain,(
% 1.52/0.56    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 1.52/0.56    inference(ennf_transformation,[],[f7])).
% 1.52/0.56  fof(f7,axiom,(
% 1.52/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).
% 1.52/0.56  fof(f90,plain,(
% 1.52/0.56    r2_hidden(k4_tarski(sK4,sK5),sK3) | r2_hidden(sK4,k10_relat_1(sK3,sK1))),
% 1.52/0.56    inference(backward_demodulation,[],[f36,f53])).
% 1.52/0.56  fof(f53,plain,(
% 1.52/0.56    ( ! [X0] : (k8_relset_1(sK0,sK2,sK3,X0) = k10_relat_1(sK3,X0)) )),
% 1.52/0.56    inference(unit_resulting_resolution,[],[f33,f50])).
% 1.52/0.56  fof(f50,plain,(
% 1.52/0.56    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.52/0.56    inference(cnf_transformation,[],[f18])).
% 1.52/0.56  fof(f18,plain,(
% 1.52/0.56    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.56    inference(ennf_transformation,[],[f8])).
% 1.52/0.56  fof(f8,axiom,(
% 1.52/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.52/0.56  fof(f36,plain,(
% 1.52/0.56    r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | r2_hidden(k4_tarski(sK4,sK5),sK3)),
% 1.52/0.56    inference(cnf_transformation,[],[f26])).
% 1.52/0.56  fof(f120,plain,(
% 1.52/0.56    ( ! [X0] : (r2_hidden(sK4,k10_relat_1(sK3,sK1)) | r2_hidden(sK4,k10_relat_1(sK3,X0)) | ~r2_hidden(sK5,X0) | ~r2_hidden(sK5,k2_relat_1(sK3))) )),
% 1.52/0.56    inference(subsumption_resolution,[],[f111,f54])).
% 1.52/0.56  fof(f111,plain,(
% 1.52/0.56    ( ! [X0] : (r2_hidden(sK4,k10_relat_1(sK3,sK1)) | r2_hidden(sK4,k10_relat_1(sK3,X0)) | ~r2_hidden(sK5,X0) | ~r2_hidden(sK5,k2_relat_1(sK3)) | ~v1_relat_1(sK3)) )),
% 1.52/0.56    inference(resolution,[],[f90,f45])).
% 1.52/0.56  fof(f45,plain,(
% 1.52/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f32])).
% 1.52/0.56  fof(f32,plain,(
% 1.52/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2) & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.52/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f31])).
% 1.52/0.56  fof(f31,plain,(
% 1.52/0.56    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2) & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2))))),
% 1.52/0.56    introduced(choice_axiom,[])).
% 1.52/0.56  fof(f30,plain,(
% 1.52/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.52/0.56    inference(rectify,[],[f29])).
% 1.52/0.56  fof(f29,plain,(
% 1.52/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.52/0.56    inference(nnf_transformation,[],[f13])).
% 1.52/0.56  fof(f13,plain,(
% 1.52/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.52/0.56    inference(ennf_transformation,[],[f6])).
% 1.52/0.56  fof(f6,axiom,(
% 1.52/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 1.52/0.56  fof(f751,plain,(
% 1.52/0.56    r2_hidden(sK5,sK1)),
% 1.52/0.56    inference(unit_resulting_resolution,[],[f749,f91])).
% 1.52/0.56  fof(f91,plain,(
% 1.52/0.56    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | r2_hidden(sK5,sK1)),
% 1.52/0.56    inference(backward_demodulation,[],[f37,f53])).
% 1.52/0.56  fof(f37,plain,(
% 1.52/0.56    r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | r2_hidden(sK5,sK1)),
% 1.52/0.56    inference(cnf_transformation,[],[f26])).
% 1.52/0.56  fof(f749,plain,(
% 1.52/0.56    ~r2_hidden(sK4,k10_relat_1(sK3,sK1))),
% 1.52/0.56    inference(subsumption_resolution,[],[f748,f54])).
% 1.52/0.56  fof(f748,plain,(
% 1.52/0.56    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~v1_relat_1(sK3)),
% 1.52/0.56    inference(duplicate_literal_removal,[],[f744])).
% 1.52/0.56  fof(f744,plain,(
% 1.52/0.56    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~v1_relat_1(sK3)),
% 1.52/0.56    inference(resolution,[],[f260,f44])).
% 1.52/0.56  fof(f44,plain,(
% 1.52/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f32])).
% 1.52/0.56  fof(f260,plain,(
% 1.52/0.56    ( ! [X0] : (~r2_hidden(sK6(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~r2_hidden(sK4,k10_relat_1(sK3,X0))) )),
% 1.52/0.56    inference(duplicate_literal_removal,[],[f254])).
% 1.52/0.56  fof(f254,plain,(
% 1.52/0.56    ( ! [X0] : (~r2_hidden(sK4,k10_relat_1(sK3,X0)) | ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~r2_hidden(sK6(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k10_relat_1(sK3,X0))) )),
% 1.52/0.56    inference(resolution,[],[f210,f147])).
% 1.52/0.56  fof(f147,plain,(
% 1.52/0.56    ( ! [X0] : (~r2_hidden(sK6(sK4,X0,sK3),sK2) | ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~r2_hidden(sK6(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k10_relat_1(sK3,X0))) )),
% 1.52/0.56    inference(subsumption_resolution,[],[f143,f54])).
% 1.52/0.56  fof(f143,plain,(
% 1.52/0.56    ( ! [X0] : (~r2_hidden(sK6(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~r2_hidden(sK6(sK4,X0,sK3),sK2) | ~r2_hidden(sK4,k10_relat_1(sK3,X0)) | ~v1_relat_1(sK3)) )),
% 1.52/0.56    inference(resolution,[],[f130,f43])).
% 1.52/0.56  fof(f43,plain,(
% 1.52/0.56    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f32])).
% 1.52/0.56  fof(f130,plain,(
% 1.52/0.56    ( ! [X0] : (~r2_hidden(k4_tarski(sK4,X0),sK3) | ~r2_hidden(X0,sK1) | ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~r2_hidden(X0,sK2)) )),
% 1.52/0.56    inference(resolution,[],[f121,f49])).
% 1.52/0.56  fof(f49,plain,(
% 1.52/0.56    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f17])).
% 1.52/0.56  fof(f17,plain,(
% 1.52/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.52/0.56    inference(ennf_transformation,[],[f3])).
% 1.52/0.56  fof(f3,axiom,(
% 1.52/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.52/0.56  fof(f121,plain,(
% 1.52/0.56    ( ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(sK4,X5),sK3) | ~r2_hidden(sK4,k10_relat_1(sK3,sK1))) )),
% 1.52/0.56    inference(forward_demodulation,[],[f38,f53])).
% 1.52/0.56  fof(f38,plain,(
% 1.52/0.56    ( ! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(sK4,X5),sK3) | ~m1_subset_1(X5,sK2) | ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) )),
% 1.52/0.56    inference(cnf_transformation,[],[f26])).
% 1.52/0.56  fof(f210,plain,(
% 1.52/0.56    ( ! [X2,X3] : (r2_hidden(sK6(X2,X3,sK3),sK2) | ~r2_hidden(X2,k10_relat_1(sK3,X3))) )),
% 1.52/0.56    inference(resolution,[],[f83,f40])).
% 1.52/0.56  fof(f40,plain,(
% 1.52/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.52/0.56    inference(cnf_transformation,[],[f28])).
% 1.52/0.56  fof(f28,plain,(
% 1.52/0.56    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.52/0.56    inference(flattening,[],[f27])).
% 1.52/0.56  fof(f27,plain,(
% 1.52/0.56    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.52/0.56    inference(nnf_transformation,[],[f1])).
% 1.52/0.56  fof(f1,axiom,(
% 1.52/0.56    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.52/0.56  fof(f83,plain,(
% 1.52/0.56    ( ! [X8,X9] : (r2_hidden(k4_tarski(X8,sK6(X8,X9,sK3)),k2_zfmisc_1(sK0,sK2)) | ~r2_hidden(X8,k10_relat_1(sK3,X9))) )),
% 1.52/0.56    inference(subsumption_resolution,[],[f81,f54])).
% 1.52/0.56  fof(f81,plain,(
% 1.52/0.56    ( ! [X8,X9] : (r2_hidden(k4_tarski(X8,sK6(X8,X9,sK3)),k2_zfmisc_1(sK0,sK2)) | ~r2_hidden(X8,k10_relat_1(sK3,X9)) | ~v1_relat_1(sK3)) )),
% 1.52/0.56    inference(resolution,[],[f57,f43])).
% 1.52/0.56  fof(f57,plain,(
% 1.52/0.56    ( ! [X1] : (~r2_hidden(X1,sK3) | r2_hidden(X1,k2_zfmisc_1(sK0,sK2))) )),
% 1.52/0.56    inference(resolution,[],[f33,f48])).
% 1.52/0.56  fof(f48,plain,(
% 1.52/0.56    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.52/0.56    inference(cnf_transformation,[],[f16])).
% 1.52/0.56  fof(f16,plain,(
% 1.52/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.52/0.56    inference(ennf_transformation,[],[f2])).
% 1.52/0.56  fof(f2,axiom,(
% 1.52/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.52/0.56  % SZS output end Proof for theBenchmark
% 1.52/0.56  % (26469)------------------------------
% 1.52/0.56  % (26469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (26469)Termination reason: Refutation
% 1.52/0.56  
% 1.52/0.56  % (26469)Memory used [KB]: 2046
% 1.52/0.56  % (26469)Time elapsed: 0.156 s
% 1.52/0.56  % (26469)------------------------------
% 1.52/0.56  % (26469)------------------------------
% 1.52/0.56  % (26451)Success in time 0.203 s
%------------------------------------------------------------------------------
