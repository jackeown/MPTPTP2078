%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:57:00 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 829 expanded)
%              Number of clauses        :   73 ( 287 expanded)
%              Number of leaves         :   18 ( 183 expanded)
%              Depth                    :   21
%              Number of atoms          :  514 (4515 expanded)
%              Number of equality atoms :  136 ( 338 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
        & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
            & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => ! [X4] :
            ( m1_subset_1(X4,X0)
           => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
            <=> ? [X5] :
                  ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X5,X4),X3)
                  & m1_subset_1(X5,X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
          <~> ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X4),X3)
                & m1_subset_1(X5,X2) ) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f41,plain,(
    ! [X4,X2,X3,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X6,X4),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK9,X1)
        & r2_hidden(k4_tarski(sK9,X4),X3)
        & m1_subset_1(sK9,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
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
     => ( ( ! [X5] :
              ( ~ r2_hidden(X5,X1)
              | ~ r2_hidden(k4_tarski(X5,sK8),X3)
              | ~ m1_subset_1(X5,X2) )
          | ~ r2_hidden(sK8,k7_relset_1(X2,X0,X3,X1)) )
        & ( ? [X6] :
              ( r2_hidden(X6,X1)
              & r2_hidden(k4_tarski(X6,sK8),X3)
              & m1_subset_1(X6,X2) )
          | r2_hidden(sK8,k7_relset_1(X2,X0,X3,X1)) )
        & m1_subset_1(sK8,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
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
                ( ~ r2_hidden(X5,sK5)
                | ~ r2_hidden(k4_tarski(X5,X4),sK7)
                | ~ m1_subset_1(X5,sK6) )
            | ~ r2_hidden(X4,k7_relset_1(sK6,sK4,sK7,sK5)) )
          & ( ? [X6] :
                ( r2_hidden(X6,sK5)
                & r2_hidden(k4_tarski(X6,X4),sK7)
                & m1_subset_1(X6,sK6) )
            | r2_hidden(X4,k7_relset_1(sK6,sK4,sK7,sK5)) )
          & m1_subset_1(X4,sK4) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( ! [X5] :
          ( ~ r2_hidden(X5,sK5)
          | ~ r2_hidden(k4_tarski(X5,sK8),sK7)
          | ~ m1_subset_1(X5,sK6) )
      | ~ r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) )
    & ( ( r2_hidden(sK9,sK5)
        & r2_hidden(k4_tarski(sK9,sK8),sK7)
        & m1_subset_1(sK9,sK6) )
      | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) )
    & m1_subset_1(sK8,sK4)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f38,f41,f40,f39])).

fof(f63,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,
    ( m1_subset_1(sK9,sK6)
    | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK5)
      | ~ r2_hidden(k4_tarski(X5,sK8),sK7)
      | ~ m1_subset_1(X5,sK6)
      | ~ r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,
    ( r2_hidden(k4_tarski(sK9,sK8),sK7)
    | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

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
    inference(nnf_transformation,[],[f18])).

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

fof(f29,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,X3),X0) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X3),X0) ) ) ),
    introduced(choice_axiom,[])).

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
              | ~ r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK0(X0,X1,X2)),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK1(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0) )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK2(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).

fof(f50,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f69,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f67,plain,
    ( r2_hidden(sK9,sK5)
    | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1915,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1913,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1906,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_18,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_12,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_344,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_18,c_12])).

cnf(c_1903,plain,
    ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_344])).

cnf(c_2316,plain,
    ( r1_tarski(k1_relat_1(sK7),sK6) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1906,c_1903])).

cnf(c_26,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2103,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(sK6,sK4))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2104,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(sK6,sK4)) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2103])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_207,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_257,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_207])).

cnf(c_2211,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_257])).

cnf(c_2378,plain,
    ( ~ r1_tarski(sK7,k2_zfmisc_1(sK6,sK4))
    | ~ v1_relat_1(k2_zfmisc_1(sK6,sK4))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2211])).

cnf(c_2379,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(sK6,sK4)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK6,sK4)) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2378])).

cnf(c_13,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2570,plain,
    ( v1_relat_1(k2_zfmisc_1(sK6,sK4)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2571,plain,
    ( v1_relat_1(k2_zfmisc_1(sK6,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2570])).

cnf(c_2575,plain,
    ( r1_tarski(k1_relat_1(sK7),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2316,c_26,c_2104,c_2379,c_2571])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_254,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_0,c_207])).

cnf(c_1905,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_254])).

cnf(c_2967,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2575,c_1905])).

cnf(c_3823,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(X0,X1,sK7),sK6) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1913,c_2967])).

cnf(c_5433,plain,
    ( r2_hidden(sK3(X0,X1,sK7),sK6) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3823,c_26,c_2104,c_2379,c_2571])).

cnf(c_5434,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(X0,X1,sK7),sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_5433])).

cnf(c_1,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1925,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5441,plain,
    ( m1_subset_1(sK3(X0,X1,sK7),sK6) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5434,c_1925])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1914,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK9,sK6)
    | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1908,plain,
    ( m1_subset_1(sK9,sK6) = iProver_top
    | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_20,negated_conjecture,
    ( ~ m1_subset_1(X0,sK6)
    | ~ r2_hidden(X0,sK5)
    | ~ r2_hidden(k4_tarski(X0,sK8),sK7)
    | ~ r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1911,plain,
    ( m1_subset_1(X0,sK6) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,sK8),sK7) != iProver_top
    | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2153,plain,
    ( m1_subset_1(X0,sK6) != iProver_top
    | m1_subset_1(sK9,sK6) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,sK8),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1908,c_1911])).

cnf(c_3891,plain,
    ( m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top
    | m1_subset_1(sK9,sK6) = iProver_top
    | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1914,c_2153])).

cnf(c_4281,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top
    | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
    | m1_subset_1(sK9,sK6) = iProver_top
    | m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3891,c_26,c_2104,c_2379,c_2571])).

cnf(c_4282,plain,
    ( m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top
    | m1_subset_1(sK9,sK6) = iProver_top
    | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4281])).

cnf(c_5694,plain,
    ( m1_subset_1(sK9,sK6) = iProver_top
    | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5441,c_4282])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1912,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3201,plain,
    ( k7_relset_1(sK6,sK4,sK7,X0) = k9_relat_1(sK7,X0) ),
    inference(superposition,[status(thm)],[c_1906,c_1912])).

cnf(c_3415,plain,
    ( m1_subset_1(X0,sK6) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,sK8),sK7) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3201,c_1911])).

cnf(c_3888,plain,
    ( m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top
    | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK5)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1914,c_3415])).

cnf(c_4495,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK5)) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top
    | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
    | m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3888,c_26,c_2104,c_2379,c_2571])).

cnf(c_4496,plain,
    ( m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top
    | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4495])).

cnf(c_5692,plain,
    ( r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5441,c_4496])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(k4_tarski(sK9,sK8),sK7)
    | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1909,plain,
    ( r2_hidden(k4_tarski(sK9,sK8),sK7) = iProver_top
    | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3412,plain,
    ( r2_hidden(k4_tarski(sK9,sK8),sK7) = iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3201,c_1909])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1919,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4073,plain,
    ( r2_hidden(sK9,X0) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,X0)) = iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3412,c_1919])).

cnf(c_5336,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,X0)) = iProver_top
    | r2_hidden(sK9,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4073,c_26,c_2104,c_2379,c_2571])).

cnf(c_5337,plain,
    ( r2_hidden(sK9,X0) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,X0)) = iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5336])).

cnf(c_5346,plain,
    ( m1_subset_1(sK8,k9_relat_1(sK7,X0)) = iProver_top
    | r2_hidden(sK9,X0) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5337,c_1925])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(sK9,sK5)
    | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1910,plain,
    ( r2_hidden(sK9,sK5) = iProver_top
    | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3413,plain,
    ( r2_hidden(sK9,sK5) = iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3201,c_1910])).

cnf(c_5347,plain,
    ( r2_hidden(sK9,sK5) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_5337])).

cnf(c_5349,plain,
    ( r2_hidden(sK9,sK5) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5347])).

cnf(c_5903,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5346,c_3413,c_5349])).

cnf(c_6094,plain,
    ( r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5694,c_3413,c_5349,c_5692])).

cnf(c_6102,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK5)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1915,c_6094])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6102,c_5903,c_2571,c_2379,c_2104,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:33:10 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.97/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.97/0.99  
% 2.97/0.99  ------  iProver source info
% 2.97/0.99  
% 2.97/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.97/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.97/0.99  git: non_committed_changes: false
% 2.97/0.99  git: last_make_outside_of_git: false
% 2.97/0.99  
% 2.97/0.99  ------ 
% 2.97/0.99  
% 2.97/0.99  ------ Input Options
% 2.97/0.99  
% 2.97/0.99  --out_options                           all
% 2.97/0.99  --tptp_safe_out                         true
% 2.97/0.99  --problem_path                          ""
% 2.97/0.99  --include_path                          ""
% 2.97/0.99  --clausifier                            res/vclausify_rel
% 2.97/0.99  --clausifier_options                    --mode clausify
% 2.97/0.99  --stdin                                 false
% 2.97/0.99  --stats_out                             all
% 2.97/0.99  
% 2.97/0.99  ------ General Options
% 2.97/0.99  
% 2.97/0.99  --fof                                   false
% 2.97/0.99  --time_out_real                         305.
% 2.97/0.99  --time_out_virtual                      -1.
% 2.97/0.99  --symbol_type_check                     false
% 2.97/0.99  --clausify_out                          false
% 2.97/0.99  --sig_cnt_out                           false
% 2.97/0.99  --trig_cnt_out                          false
% 2.97/0.99  --trig_cnt_out_tolerance                1.
% 2.97/0.99  --trig_cnt_out_sk_spl                   false
% 2.97/0.99  --abstr_cl_out                          false
% 2.97/0.99  
% 2.97/0.99  ------ Global Options
% 2.97/0.99  
% 2.97/0.99  --schedule                              default
% 2.97/0.99  --add_important_lit                     false
% 2.97/0.99  --prop_solver_per_cl                    1000
% 2.97/0.99  --min_unsat_core                        false
% 2.97/0.99  --soft_assumptions                      false
% 2.97/0.99  --soft_lemma_size                       3
% 2.97/0.99  --prop_impl_unit_size                   0
% 2.97/0.99  --prop_impl_unit                        []
% 2.97/0.99  --share_sel_clauses                     true
% 2.97/0.99  --reset_solvers                         false
% 2.97/0.99  --bc_imp_inh                            [conj_cone]
% 2.97/0.99  --conj_cone_tolerance                   3.
% 2.97/0.99  --extra_neg_conj                        none
% 2.97/0.99  --large_theory_mode                     true
% 2.97/0.99  --prolific_symb_bound                   200
% 2.97/0.99  --lt_threshold                          2000
% 2.97/0.99  --clause_weak_htbl                      true
% 2.97/0.99  --gc_record_bc_elim                     false
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing Options
% 2.97/0.99  
% 2.97/0.99  --preprocessing_flag                    true
% 2.97/0.99  --time_out_prep_mult                    0.1
% 2.97/0.99  --splitting_mode                        input
% 2.97/0.99  --splitting_grd                         true
% 2.97/0.99  --splitting_cvd                         false
% 2.97/0.99  --splitting_cvd_svl                     false
% 2.97/0.99  --splitting_nvd                         32
% 2.97/0.99  --sub_typing                            true
% 2.97/0.99  --prep_gs_sim                           true
% 2.97/0.99  --prep_unflatten                        true
% 2.97/0.99  --prep_res_sim                          true
% 2.97/0.99  --prep_upred                            true
% 2.97/0.99  --prep_sem_filter                       exhaustive
% 2.97/0.99  --prep_sem_filter_out                   false
% 2.97/0.99  --pred_elim                             true
% 2.97/0.99  --res_sim_input                         true
% 2.97/0.99  --eq_ax_congr_red                       true
% 2.97/0.99  --pure_diseq_elim                       true
% 2.97/0.99  --brand_transform                       false
% 2.97/0.99  --non_eq_to_eq                          false
% 2.97/0.99  --prep_def_merge                        true
% 2.97/0.99  --prep_def_merge_prop_impl              false
% 2.97/0.99  --prep_def_merge_mbd                    true
% 2.97/0.99  --prep_def_merge_tr_red                 false
% 2.97/0.99  --prep_def_merge_tr_cl                  false
% 2.97/0.99  --smt_preprocessing                     true
% 2.97/0.99  --smt_ac_axioms                         fast
% 2.97/0.99  --preprocessed_out                      false
% 2.97/0.99  --preprocessed_stats                    false
% 2.97/0.99  
% 2.97/0.99  ------ Abstraction refinement Options
% 2.97/0.99  
% 2.97/0.99  --abstr_ref                             []
% 2.97/0.99  --abstr_ref_prep                        false
% 2.97/0.99  --abstr_ref_until_sat                   false
% 2.97/0.99  --abstr_ref_sig_restrict                funpre
% 2.97/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/0.99  --abstr_ref_under                       []
% 2.97/0.99  
% 2.97/0.99  ------ SAT Options
% 2.97/0.99  
% 2.97/0.99  --sat_mode                              false
% 2.97/0.99  --sat_fm_restart_options                ""
% 2.97/0.99  --sat_gr_def                            false
% 2.97/0.99  --sat_epr_types                         true
% 2.97/0.99  --sat_non_cyclic_types                  false
% 2.97/0.99  --sat_finite_models                     false
% 2.97/0.99  --sat_fm_lemmas                         false
% 2.97/0.99  --sat_fm_prep                           false
% 2.97/0.99  --sat_fm_uc_incr                        true
% 2.97/0.99  --sat_out_model                         small
% 2.97/0.99  --sat_out_clauses                       false
% 2.97/0.99  
% 2.97/0.99  ------ QBF Options
% 2.97/0.99  
% 2.97/0.99  --qbf_mode                              false
% 2.97/0.99  --qbf_elim_univ                         false
% 2.97/0.99  --qbf_dom_inst                          none
% 2.97/0.99  --qbf_dom_pre_inst                      false
% 2.97/0.99  --qbf_sk_in                             false
% 2.97/0.99  --qbf_pred_elim                         true
% 2.97/0.99  --qbf_split                             512
% 2.97/0.99  
% 2.97/0.99  ------ BMC1 Options
% 2.97/0.99  
% 2.97/0.99  --bmc1_incremental                      false
% 2.97/0.99  --bmc1_axioms                           reachable_all
% 2.97/0.99  --bmc1_min_bound                        0
% 2.97/0.99  --bmc1_max_bound                        -1
% 2.97/0.99  --bmc1_max_bound_default                -1
% 2.97/0.99  --bmc1_symbol_reachability              true
% 2.97/0.99  --bmc1_property_lemmas                  false
% 2.97/0.99  --bmc1_k_induction                      false
% 2.97/0.99  --bmc1_non_equiv_states                 false
% 2.97/0.99  --bmc1_deadlock                         false
% 2.97/0.99  --bmc1_ucm                              false
% 2.97/0.99  --bmc1_add_unsat_core                   none
% 2.97/0.99  --bmc1_unsat_core_children              false
% 2.97/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/0.99  --bmc1_out_stat                         full
% 2.97/0.99  --bmc1_ground_init                      false
% 2.97/0.99  --bmc1_pre_inst_next_state              false
% 2.97/0.99  --bmc1_pre_inst_state                   false
% 2.97/0.99  --bmc1_pre_inst_reach_state             false
% 2.97/0.99  --bmc1_out_unsat_core                   false
% 2.97/0.99  --bmc1_aig_witness_out                  false
% 2.97/0.99  --bmc1_verbose                          false
% 2.97/0.99  --bmc1_dump_clauses_tptp                false
% 2.97/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.97/0.99  --bmc1_dump_file                        -
% 2.97/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.97/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.97/0.99  --bmc1_ucm_extend_mode                  1
% 2.97/0.99  --bmc1_ucm_init_mode                    2
% 2.97/0.99  --bmc1_ucm_cone_mode                    none
% 2.97/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.97/0.99  --bmc1_ucm_relax_model                  4
% 2.97/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.97/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/0.99  --bmc1_ucm_layered_model                none
% 2.97/0.99  --bmc1_ucm_max_lemma_size               10
% 2.97/0.99  
% 2.97/0.99  ------ AIG Options
% 2.97/0.99  
% 2.97/0.99  --aig_mode                              false
% 2.97/0.99  
% 2.97/0.99  ------ Instantiation Options
% 2.97/0.99  
% 2.97/0.99  --instantiation_flag                    true
% 2.97/0.99  --inst_sos_flag                         false
% 2.97/0.99  --inst_sos_phase                        true
% 2.97/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel_side                     num_symb
% 2.97/0.99  --inst_solver_per_active                1400
% 2.97/0.99  --inst_solver_calls_frac                1.
% 2.97/0.99  --inst_passive_queue_type               priority_queues
% 2.97/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/0.99  --inst_passive_queues_freq              [25;2]
% 2.97/0.99  --inst_dismatching                      true
% 2.97/0.99  --inst_eager_unprocessed_to_passive     true
% 2.97/0.99  --inst_prop_sim_given                   true
% 2.97/0.99  --inst_prop_sim_new                     false
% 2.97/0.99  --inst_subs_new                         false
% 2.97/0.99  --inst_eq_res_simp                      false
% 2.97/0.99  --inst_subs_given                       false
% 2.97/0.99  --inst_orphan_elimination               true
% 2.97/0.99  --inst_learning_loop_flag               true
% 2.97/0.99  --inst_learning_start                   3000
% 2.97/0.99  --inst_learning_factor                  2
% 2.97/0.99  --inst_start_prop_sim_after_learn       3
% 2.97/0.99  --inst_sel_renew                        solver
% 2.97/0.99  --inst_lit_activity_flag                true
% 2.97/0.99  --inst_restr_to_given                   false
% 2.97/0.99  --inst_activity_threshold               500
% 2.97/0.99  --inst_out_proof                        true
% 2.97/0.99  
% 2.97/0.99  ------ Resolution Options
% 2.97/0.99  
% 2.97/0.99  --resolution_flag                       true
% 2.97/0.99  --res_lit_sel                           adaptive
% 2.97/0.99  --res_lit_sel_side                      none
% 2.97/0.99  --res_ordering                          kbo
% 2.97/0.99  --res_to_prop_solver                    active
% 2.97/0.99  --res_prop_simpl_new                    false
% 2.97/0.99  --res_prop_simpl_given                  true
% 2.97/0.99  --res_passive_queue_type                priority_queues
% 2.97/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/0.99  --res_passive_queues_freq               [15;5]
% 2.97/0.99  --res_forward_subs                      full
% 2.97/0.99  --res_backward_subs                     full
% 2.97/0.99  --res_forward_subs_resolution           true
% 2.97/0.99  --res_backward_subs_resolution          true
% 2.97/0.99  --res_orphan_elimination                true
% 2.97/0.99  --res_time_limit                        2.
% 2.97/0.99  --res_out_proof                         true
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Options
% 2.97/0.99  
% 2.97/0.99  --superposition_flag                    true
% 2.97/0.99  --sup_passive_queue_type                priority_queues
% 2.97/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.97/0.99  --demod_completeness_check              fast
% 2.97/0.99  --demod_use_ground                      true
% 2.97/0.99  --sup_to_prop_solver                    passive
% 2.97/0.99  --sup_prop_simpl_new                    true
% 2.97/0.99  --sup_prop_simpl_given                  true
% 2.97/0.99  --sup_fun_splitting                     false
% 2.97/0.99  --sup_smt_interval                      50000
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Simplification Setup
% 2.97/0.99  
% 2.97/0.99  --sup_indices_passive                   []
% 2.97/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_full_bw                           [BwDemod]
% 2.97/0.99  --sup_immed_triv                        [TrivRules]
% 2.97/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_immed_bw_main                     []
% 2.97/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  
% 2.97/0.99  ------ Combination Options
% 2.97/0.99  
% 2.97/0.99  --comb_res_mult                         3
% 2.97/0.99  --comb_sup_mult                         2
% 2.97/0.99  --comb_inst_mult                        10
% 2.97/0.99  
% 2.97/0.99  ------ Debug Options
% 2.97/0.99  
% 2.97/0.99  --dbg_backtrace                         false
% 2.97/0.99  --dbg_dump_prop_clauses                 false
% 2.97/0.99  --dbg_dump_prop_clauses_file            -
% 2.97/0.99  --dbg_out_stat                          false
% 2.97/0.99  ------ Parsing...
% 2.97/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.97/0.99  ------ Proving...
% 2.97/0.99  ------ Problem Properties 
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  clauses                                 23
% 2.97/0.99  conjectures                             6
% 2.97/0.99  EPR                                     4
% 2.97/0.99  Horn                                    18
% 2.97/0.99  unary                                   3
% 2.97/0.99  binary                                  7
% 2.97/0.99  lits                                    62
% 2.97/0.99  lits eq                                 4
% 2.97/0.99  fd_pure                                 0
% 2.97/0.99  fd_pseudo                               0
% 2.97/0.99  fd_cond                                 0
% 2.97/0.99  fd_pseudo_cond                          3
% 2.97/0.99  AC symbols                              0
% 2.97/0.99  
% 2.97/0.99  ------ Schedule dynamic 5 is on 
% 2.97/0.99  
% 2.97/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  ------ 
% 2.97/0.99  Current options:
% 2.97/0.99  ------ 
% 2.97/0.99  
% 2.97/0.99  ------ Input Options
% 2.97/0.99  
% 2.97/0.99  --out_options                           all
% 2.97/0.99  --tptp_safe_out                         true
% 2.97/0.99  --problem_path                          ""
% 2.97/0.99  --include_path                          ""
% 2.97/0.99  --clausifier                            res/vclausify_rel
% 2.97/0.99  --clausifier_options                    --mode clausify
% 2.97/0.99  --stdin                                 false
% 2.97/0.99  --stats_out                             all
% 2.97/0.99  
% 2.97/0.99  ------ General Options
% 2.97/0.99  
% 2.97/0.99  --fof                                   false
% 2.97/0.99  --time_out_real                         305.
% 2.97/0.99  --time_out_virtual                      -1.
% 2.97/0.99  --symbol_type_check                     false
% 2.97/0.99  --clausify_out                          false
% 2.97/0.99  --sig_cnt_out                           false
% 2.97/0.99  --trig_cnt_out                          false
% 2.97/0.99  --trig_cnt_out_tolerance                1.
% 2.97/0.99  --trig_cnt_out_sk_spl                   false
% 2.97/0.99  --abstr_cl_out                          false
% 2.97/0.99  
% 2.97/0.99  ------ Global Options
% 2.97/0.99  
% 2.97/0.99  --schedule                              default
% 2.97/0.99  --add_important_lit                     false
% 2.97/0.99  --prop_solver_per_cl                    1000
% 2.97/0.99  --min_unsat_core                        false
% 2.97/0.99  --soft_assumptions                      false
% 2.97/0.99  --soft_lemma_size                       3
% 2.97/0.99  --prop_impl_unit_size                   0
% 2.97/0.99  --prop_impl_unit                        []
% 2.97/0.99  --share_sel_clauses                     true
% 2.97/0.99  --reset_solvers                         false
% 2.97/0.99  --bc_imp_inh                            [conj_cone]
% 2.97/0.99  --conj_cone_tolerance                   3.
% 2.97/0.99  --extra_neg_conj                        none
% 2.97/0.99  --large_theory_mode                     true
% 2.97/0.99  --prolific_symb_bound                   200
% 2.97/0.99  --lt_threshold                          2000
% 2.97/0.99  --clause_weak_htbl                      true
% 2.97/0.99  --gc_record_bc_elim                     false
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing Options
% 2.97/0.99  
% 2.97/0.99  --preprocessing_flag                    true
% 2.97/0.99  --time_out_prep_mult                    0.1
% 2.97/0.99  --splitting_mode                        input
% 2.97/0.99  --splitting_grd                         true
% 2.97/0.99  --splitting_cvd                         false
% 2.97/0.99  --splitting_cvd_svl                     false
% 2.97/0.99  --splitting_nvd                         32
% 2.97/0.99  --sub_typing                            true
% 2.97/0.99  --prep_gs_sim                           true
% 2.97/0.99  --prep_unflatten                        true
% 2.97/0.99  --prep_res_sim                          true
% 2.97/0.99  --prep_upred                            true
% 2.97/0.99  --prep_sem_filter                       exhaustive
% 2.97/0.99  --prep_sem_filter_out                   false
% 2.97/0.99  --pred_elim                             true
% 2.97/0.99  --res_sim_input                         true
% 2.97/0.99  --eq_ax_congr_red                       true
% 2.97/0.99  --pure_diseq_elim                       true
% 2.97/0.99  --brand_transform                       false
% 2.97/0.99  --non_eq_to_eq                          false
% 2.97/0.99  --prep_def_merge                        true
% 2.97/0.99  --prep_def_merge_prop_impl              false
% 2.97/0.99  --prep_def_merge_mbd                    true
% 2.97/0.99  --prep_def_merge_tr_red                 false
% 2.97/0.99  --prep_def_merge_tr_cl                  false
% 2.97/0.99  --smt_preprocessing                     true
% 2.97/0.99  --smt_ac_axioms                         fast
% 2.97/0.99  --preprocessed_out                      false
% 2.97/0.99  --preprocessed_stats                    false
% 2.97/0.99  
% 2.97/0.99  ------ Abstraction refinement Options
% 2.97/0.99  
% 2.97/0.99  --abstr_ref                             []
% 2.97/0.99  --abstr_ref_prep                        false
% 2.97/0.99  --abstr_ref_until_sat                   false
% 2.97/0.99  --abstr_ref_sig_restrict                funpre
% 2.97/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/0.99  --abstr_ref_under                       []
% 2.97/0.99  
% 2.97/0.99  ------ SAT Options
% 2.97/0.99  
% 2.97/0.99  --sat_mode                              false
% 2.97/0.99  --sat_fm_restart_options                ""
% 2.97/0.99  --sat_gr_def                            false
% 2.97/0.99  --sat_epr_types                         true
% 2.97/0.99  --sat_non_cyclic_types                  false
% 2.97/0.99  --sat_finite_models                     false
% 2.97/0.99  --sat_fm_lemmas                         false
% 2.97/0.99  --sat_fm_prep                           false
% 2.97/0.99  --sat_fm_uc_incr                        true
% 2.97/0.99  --sat_out_model                         small
% 2.97/0.99  --sat_out_clauses                       false
% 2.97/0.99  
% 2.97/0.99  ------ QBF Options
% 2.97/0.99  
% 2.97/0.99  --qbf_mode                              false
% 2.97/0.99  --qbf_elim_univ                         false
% 2.97/0.99  --qbf_dom_inst                          none
% 2.97/0.99  --qbf_dom_pre_inst                      false
% 2.97/0.99  --qbf_sk_in                             false
% 2.97/0.99  --qbf_pred_elim                         true
% 2.97/0.99  --qbf_split                             512
% 2.97/0.99  
% 2.97/0.99  ------ BMC1 Options
% 2.97/0.99  
% 2.97/0.99  --bmc1_incremental                      false
% 2.97/0.99  --bmc1_axioms                           reachable_all
% 2.97/0.99  --bmc1_min_bound                        0
% 2.97/0.99  --bmc1_max_bound                        -1
% 2.97/0.99  --bmc1_max_bound_default                -1
% 2.97/0.99  --bmc1_symbol_reachability              true
% 2.97/0.99  --bmc1_property_lemmas                  false
% 2.97/0.99  --bmc1_k_induction                      false
% 2.97/0.99  --bmc1_non_equiv_states                 false
% 2.97/0.99  --bmc1_deadlock                         false
% 2.97/0.99  --bmc1_ucm                              false
% 2.97/0.99  --bmc1_add_unsat_core                   none
% 2.97/0.99  --bmc1_unsat_core_children              false
% 2.97/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/0.99  --bmc1_out_stat                         full
% 2.97/0.99  --bmc1_ground_init                      false
% 2.97/0.99  --bmc1_pre_inst_next_state              false
% 2.97/0.99  --bmc1_pre_inst_state                   false
% 2.97/0.99  --bmc1_pre_inst_reach_state             false
% 2.97/0.99  --bmc1_out_unsat_core                   false
% 2.97/0.99  --bmc1_aig_witness_out                  false
% 2.97/0.99  --bmc1_verbose                          false
% 2.97/0.99  --bmc1_dump_clauses_tptp                false
% 2.97/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.97/0.99  --bmc1_dump_file                        -
% 2.97/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.97/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.97/0.99  --bmc1_ucm_extend_mode                  1
% 2.97/0.99  --bmc1_ucm_init_mode                    2
% 2.97/0.99  --bmc1_ucm_cone_mode                    none
% 2.97/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.97/0.99  --bmc1_ucm_relax_model                  4
% 2.97/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.97/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/0.99  --bmc1_ucm_layered_model                none
% 2.97/0.99  --bmc1_ucm_max_lemma_size               10
% 2.97/0.99  
% 2.97/0.99  ------ AIG Options
% 2.97/0.99  
% 2.97/0.99  --aig_mode                              false
% 2.97/0.99  
% 2.97/0.99  ------ Instantiation Options
% 2.97/0.99  
% 2.97/0.99  --instantiation_flag                    true
% 2.97/0.99  --inst_sos_flag                         false
% 2.97/0.99  --inst_sos_phase                        true
% 2.97/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel_side                     none
% 2.97/0.99  --inst_solver_per_active                1400
% 2.97/0.99  --inst_solver_calls_frac                1.
% 2.97/0.99  --inst_passive_queue_type               priority_queues
% 2.97/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/0.99  --inst_passive_queues_freq              [25;2]
% 2.97/0.99  --inst_dismatching                      true
% 2.97/0.99  --inst_eager_unprocessed_to_passive     true
% 2.97/0.99  --inst_prop_sim_given                   true
% 2.97/0.99  --inst_prop_sim_new                     false
% 2.97/0.99  --inst_subs_new                         false
% 2.97/0.99  --inst_eq_res_simp                      false
% 2.97/0.99  --inst_subs_given                       false
% 2.97/0.99  --inst_orphan_elimination               true
% 2.97/0.99  --inst_learning_loop_flag               true
% 2.97/0.99  --inst_learning_start                   3000
% 2.97/0.99  --inst_learning_factor                  2
% 2.97/0.99  --inst_start_prop_sim_after_learn       3
% 2.97/0.99  --inst_sel_renew                        solver
% 2.97/0.99  --inst_lit_activity_flag                true
% 2.97/0.99  --inst_restr_to_given                   false
% 2.97/0.99  --inst_activity_threshold               500
% 2.97/0.99  --inst_out_proof                        true
% 2.97/0.99  
% 2.97/0.99  ------ Resolution Options
% 2.97/0.99  
% 2.97/0.99  --resolution_flag                       false
% 2.97/0.99  --res_lit_sel                           adaptive
% 2.97/0.99  --res_lit_sel_side                      none
% 2.97/0.99  --res_ordering                          kbo
% 2.97/0.99  --res_to_prop_solver                    active
% 2.97/0.99  --res_prop_simpl_new                    false
% 2.97/0.99  --res_prop_simpl_given                  true
% 2.97/0.99  --res_passive_queue_type                priority_queues
% 2.97/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/0.99  --res_passive_queues_freq               [15;5]
% 2.97/0.99  --res_forward_subs                      full
% 2.97/0.99  --res_backward_subs                     full
% 2.97/0.99  --res_forward_subs_resolution           true
% 2.97/0.99  --res_backward_subs_resolution          true
% 2.97/0.99  --res_orphan_elimination                true
% 2.97/0.99  --res_time_limit                        2.
% 2.97/0.99  --res_out_proof                         true
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Options
% 2.97/0.99  
% 2.97/0.99  --superposition_flag                    true
% 2.97/0.99  --sup_passive_queue_type                priority_queues
% 2.97/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.97/0.99  --demod_completeness_check              fast
% 2.97/0.99  --demod_use_ground                      true
% 2.97/0.99  --sup_to_prop_solver                    passive
% 2.97/0.99  --sup_prop_simpl_new                    true
% 2.97/0.99  --sup_prop_simpl_given                  true
% 2.97/0.99  --sup_fun_splitting                     false
% 2.97/0.99  --sup_smt_interval                      50000
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Simplification Setup
% 2.97/0.99  
% 2.97/0.99  --sup_indices_passive                   []
% 2.97/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_full_bw                           [BwDemod]
% 2.97/0.99  --sup_immed_triv                        [TrivRules]
% 2.97/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_immed_bw_main                     []
% 2.97/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  
% 2.97/0.99  ------ Combination Options
% 2.97/0.99  
% 2.97/0.99  --comb_res_mult                         3
% 2.97/0.99  --comb_sup_mult                         2
% 2.97/0.99  --comb_inst_mult                        10
% 2.97/0.99  
% 2.97/0.99  ------ Debug Options
% 2.97/0.99  
% 2.97/0.99  --dbg_backtrace                         false
% 2.97/0.99  --dbg_dump_prop_clauses                 false
% 2.97/0.99  --dbg_dump_prop_clauses_file            -
% 2.97/0.99  --dbg_out_stat                          false
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  ------ Proving...
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  % SZS status Theorem for theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  fof(f8,axiom,(
% 2.97/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f20,plain,(
% 2.97/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 2.97/0.99    inference(ennf_transformation,[],[f8])).
% 2.97/0.99  
% 2.97/0.99  fof(f32,plain,(
% 2.97/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.97/0.99    inference(nnf_transformation,[],[f20])).
% 2.97/0.99  
% 2.97/0.99  fof(f33,plain,(
% 2.97/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.97/0.99    inference(rectify,[],[f32])).
% 2.97/0.99  
% 2.97/0.99  fof(f34,plain,(
% 2.97/0.99    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))))),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f35,plain,(
% 2.97/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).
% 2.97/0.99  
% 2.97/0.99  fof(f59,plain,(
% 2.97/0.99    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f35])).
% 2.97/0.99  
% 2.97/0.99  fof(f57,plain,(
% 2.97/0.99    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f35])).
% 2.97/0.99  
% 2.97/0.99  fof(f11,conjecture,(
% 2.97/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f12,negated_conjecture,(
% 2.97/0.99    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 2.97/0.99    inference(negated_conjecture,[],[f11])).
% 2.97/0.99  
% 2.97/0.99  fof(f13,plain,(
% 2.97/0.99    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)))))),
% 2.97/0.99    inference(pure_predicate_removal,[],[f12])).
% 2.97/0.99  
% 2.97/0.99  fof(f23,plain,(
% 2.97/0.99    ? [X0,X1,X2,X3] : (? [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 2.97/0.99    inference(ennf_transformation,[],[f13])).
% 2.97/0.99  
% 2.97/0.99  fof(f36,plain,(
% 2.97/0.99    ? [X0,X1,X2,X3] : (? [X4] : (((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 2.97/0.99    inference(nnf_transformation,[],[f23])).
% 2.97/0.99  
% 2.97/0.99  fof(f37,plain,(
% 2.97/0.99    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 2.97/0.99    inference(flattening,[],[f36])).
% 2.97/0.99  
% 2.97/0.99  fof(f38,plain,(
% 2.97/0.99    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 2.97/0.99    inference(rectify,[],[f37])).
% 2.97/0.99  
% 2.97/0.99  fof(f41,plain,(
% 2.97/0.99    ( ! [X4,X2,X3,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK9,X1) & r2_hidden(k4_tarski(sK9,X4),X3) & m1_subset_1(sK9,X2))) )),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f40,plain,(
% 2.97/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) => ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,sK8),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(sK8,k7_relset_1(X2,X0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,sK8),X3) & m1_subset_1(X6,X2)) | r2_hidden(sK8,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(sK8,X0))) )),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f39,plain,(
% 2.97/0.99    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) => (? [X4] : ((! [X5] : (~r2_hidden(X5,sK5) | ~r2_hidden(k4_tarski(X5,X4),sK7) | ~m1_subset_1(X5,sK6)) | ~r2_hidden(X4,k7_relset_1(sK6,sK4,sK7,sK5))) & (? [X6] : (r2_hidden(X6,sK5) & r2_hidden(k4_tarski(X6,X4),sK7) & m1_subset_1(X6,sK6)) | r2_hidden(X4,k7_relset_1(sK6,sK4,sK7,sK5))) & m1_subset_1(X4,sK4)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))))),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f42,plain,(
% 2.97/0.99    ((! [X5] : (~r2_hidden(X5,sK5) | ~r2_hidden(k4_tarski(X5,sK8),sK7) | ~m1_subset_1(X5,sK6)) | ~r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5))) & ((r2_hidden(sK9,sK5) & r2_hidden(k4_tarski(sK9,sK8),sK7) & m1_subset_1(sK9,sK6)) | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5))) & m1_subset_1(sK8,sK4)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))),
% 2.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f38,f41,f40,f39])).
% 2.97/0.99  
% 2.97/0.99  fof(f63,plain,(
% 2.97/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))),
% 2.97/0.99    inference(cnf_transformation,[],[f42])).
% 2.97/0.99  
% 2.97/0.99  fof(f9,axiom,(
% 2.97/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f14,plain,(
% 2.97/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.97/0.99    inference(pure_predicate_removal,[],[f9])).
% 2.97/0.99  
% 2.97/0.99  fof(f21,plain,(
% 2.97/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.99    inference(ennf_transformation,[],[f14])).
% 2.97/0.99  
% 2.97/0.99  fof(f61,plain,(
% 2.97/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f21])).
% 2.97/0.99  
% 2.97/0.99  fof(f6,axiom,(
% 2.97/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f19,plain,(
% 2.97/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.97/0.99    inference(ennf_transformation,[],[f6])).
% 2.97/0.99  
% 2.97/0.99  fof(f31,plain,(
% 2.97/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.97/0.99    inference(nnf_transformation,[],[f19])).
% 2.97/0.99  
% 2.97/0.99  fof(f54,plain,(
% 2.97/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f31])).
% 2.97/0.99  
% 2.97/0.99  fof(f3,axiom,(
% 2.97/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f24,plain,(
% 2.97/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.97/0.99    inference(nnf_transformation,[],[f3])).
% 2.97/0.99  
% 2.97/0.99  fof(f45,plain,(
% 2.97/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f24])).
% 2.97/0.99  
% 2.97/0.99  fof(f4,axiom,(
% 2.97/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f17,plain,(
% 2.97/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.97/0.99    inference(ennf_transformation,[],[f4])).
% 2.97/0.99  
% 2.97/0.99  fof(f47,plain,(
% 2.97/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f17])).
% 2.97/0.99  
% 2.97/0.99  fof(f46,plain,(
% 2.97/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f24])).
% 2.97/0.99  
% 2.97/0.99  fof(f7,axiom,(
% 2.97/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f56,plain,(
% 2.97/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f7])).
% 2.97/0.99  
% 2.97/0.99  fof(f1,axiom,(
% 2.97/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f15,plain,(
% 2.97/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.97/0.99    inference(ennf_transformation,[],[f1])).
% 2.97/0.99  
% 2.97/0.99  fof(f43,plain,(
% 2.97/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f15])).
% 2.97/0.99  
% 2.97/0.99  fof(f2,axiom,(
% 2.97/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f16,plain,(
% 2.97/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.97/0.99    inference(ennf_transformation,[],[f2])).
% 2.97/0.99  
% 2.97/0.99  fof(f44,plain,(
% 2.97/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f16])).
% 2.97/0.99  
% 2.97/0.99  fof(f58,plain,(
% 2.97/0.99    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f35])).
% 2.97/0.99  
% 2.97/0.99  fof(f65,plain,(
% 2.97/0.99    m1_subset_1(sK9,sK6) | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5))),
% 2.97/0.99    inference(cnf_transformation,[],[f42])).
% 2.97/0.99  
% 2.97/0.99  fof(f68,plain,(
% 2.97/0.99    ( ! [X5] : (~r2_hidden(X5,sK5) | ~r2_hidden(k4_tarski(X5,sK8),sK7) | ~m1_subset_1(X5,sK6) | ~r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f42])).
% 2.97/0.99  
% 2.97/0.99  fof(f10,axiom,(
% 2.97/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f22,plain,(
% 2.97/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.99    inference(ennf_transformation,[],[f10])).
% 2.97/0.99  
% 2.97/0.99  fof(f62,plain,(
% 2.97/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f22])).
% 2.97/0.99  
% 2.97/0.99  fof(f66,plain,(
% 2.97/0.99    r2_hidden(k4_tarski(sK9,sK8),sK7) | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5))),
% 2.97/0.99    inference(cnf_transformation,[],[f42])).
% 2.97/0.99  
% 2.97/0.99  fof(f5,axiom,(
% 2.97/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f18,plain,(
% 2.97/0.99    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 2.97/0.99    inference(ennf_transformation,[],[f5])).
% 2.97/0.99  
% 2.97/0.99  fof(f25,plain,(
% 2.97/0.99    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 2.97/0.99    inference(nnf_transformation,[],[f18])).
% 2.97/0.99  
% 2.97/0.99  fof(f26,plain,(
% 2.97/0.99    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 2.97/0.99    inference(rectify,[],[f25])).
% 2.97/0.99  
% 2.97/0.99  fof(f29,plain,(
% 2.97/0.99    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) => (r2_hidden(sK2(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0)))),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f28,plain,(
% 2.97/0.99    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X3),X0)))) )),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f27,plain,(
% 2.97/0.99    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK0(X0,X1,X2)),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f30,plain,(
% 2.97/0.99    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & ((r2_hidden(sK2(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 2.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).
% 2.97/0.99  
% 2.97/0.99  fof(f50,plain,(
% 2.97/0.99    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f30])).
% 2.97/0.99  
% 2.97/0.99  fof(f69,plain,(
% 2.97/0.99    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k9_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | ~v1_relat_1(X0)) )),
% 2.97/0.99    inference(equality_resolution,[],[f50])).
% 2.97/0.99  
% 2.97/0.99  fof(f67,plain,(
% 2.97/0.99    r2_hidden(sK9,sK5) | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5))),
% 2.97/0.99    inference(cnf_transformation,[],[f42])).
% 2.97/0.99  
% 2.97/0.99  cnf(c_15,plain,
% 2.97/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.97/0.99      | r2_hidden(sK3(X0,X2,X1),X2)
% 2.97/0.99      | ~ v1_relat_1(X1) ),
% 2.97/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1915,plain,
% 2.97/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.97/0.99      | r2_hidden(sK3(X0,X2,X1),X2) = iProver_top
% 2.97/0.99      | v1_relat_1(X1) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_17,plain,
% 2.97/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.97/0.99      | r2_hidden(sK3(X0,X2,X1),k1_relat_1(X1))
% 2.97/0.99      | ~ v1_relat_1(X1) ),
% 2.97/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1913,plain,
% 2.97/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.97/0.99      | r2_hidden(sK3(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 2.97/0.99      | v1_relat_1(X1) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_25,negated_conjecture,
% 2.97/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
% 2.97/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1906,plain,
% 2.97/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_18,plain,
% 2.97/0.99      ( v4_relat_1(X0,X1)
% 2.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.97/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_12,plain,
% 2.97/0.99      ( ~ v4_relat_1(X0,X1)
% 2.97/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 2.97/0.99      | ~ v1_relat_1(X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_344,plain,
% 2.97/0.99      ( r1_tarski(k1_relat_1(X0),X1)
% 2.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.99      | ~ v1_relat_1(X0) ),
% 2.97/0.99      inference(resolution,[status(thm)],[c_18,c_12]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1903,plain,
% 2.97/0.99      ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 2.97/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.97/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_344]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2316,plain,
% 2.97/0.99      ( r1_tarski(k1_relat_1(sK7),sK6) = iProver_top
% 2.97/0.99      | v1_relat_1(sK7) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_1906,c_1903]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_26,plain,
% 2.97/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3,plain,
% 2.97/0.99      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.97/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2103,plain,
% 2.97/0.99      ( r1_tarski(sK7,k2_zfmisc_1(sK6,sK4))
% 2.97/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2104,plain,
% 2.97/0.99      ( r1_tarski(sK7,k2_zfmisc_1(sK6,sK4)) = iProver_top
% 2.97/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_2103]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4,plain,
% 2.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.97/0.99      | ~ v1_relat_1(X1)
% 2.97/0.99      | v1_relat_1(X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2,plain,
% 2.97/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.97/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_207,plain,
% 2.97/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.97/0.99      inference(prop_impl,[status(thm)],[c_2]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_257,plain,
% 2.97/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.97/0.99      inference(bin_hyper_res,[status(thm)],[c_4,c_207]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2211,plain,
% 2.97/0.99      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 2.97/0.99      | v1_relat_1(X0)
% 2.97/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_257]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2378,plain,
% 2.97/0.99      ( ~ r1_tarski(sK7,k2_zfmisc_1(sK6,sK4))
% 2.97/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK6,sK4))
% 2.97/0.99      | v1_relat_1(sK7) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_2211]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2379,plain,
% 2.97/0.99      ( r1_tarski(sK7,k2_zfmisc_1(sK6,sK4)) != iProver_top
% 2.97/0.99      | v1_relat_1(k2_zfmisc_1(sK6,sK4)) != iProver_top
% 2.97/0.99      | v1_relat_1(sK7) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_2378]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_13,plain,
% 2.97/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.97/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2570,plain,
% 2.97/0.99      ( v1_relat_1(k2_zfmisc_1(sK6,sK4)) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2571,plain,
% 2.97/0.99      ( v1_relat_1(k2_zfmisc_1(sK6,sK4)) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_2570]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2575,plain,
% 2.97/0.99      ( r1_tarski(k1_relat_1(sK7),sK6) = iProver_top ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_2316,c_26,c_2104,c_2379,c_2571]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_0,plain,
% 2.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.97/0.99      | ~ r2_hidden(X2,X0)
% 2.97/0.99      | r2_hidden(X2,X1) ),
% 2.97/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_254,plain,
% 2.97/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 2.97/0.99      inference(bin_hyper_res,[status(thm)],[c_0,c_207]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1905,plain,
% 2.97/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.97/0.99      | r2_hidden(X2,X0) != iProver_top
% 2.97/0.99      | r2_hidden(X2,X1) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_254]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2967,plain,
% 2.97/0.99      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 2.97/0.99      | r2_hidden(X0,sK6) = iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_2575,c_1905]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3823,plain,
% 2.97/0.99      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 2.97/0.99      | r2_hidden(sK3(X0,X1,sK7),sK6) = iProver_top
% 2.97/0.99      | v1_relat_1(sK7) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_1913,c_2967]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_5433,plain,
% 2.97/0.99      ( r2_hidden(sK3(X0,X1,sK7),sK6) = iProver_top
% 2.97/0.99      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_3823,c_26,c_2104,c_2379,c_2571]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_5434,plain,
% 2.97/0.99      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 2.97/0.99      | r2_hidden(sK3(X0,X1,sK7),sK6) = iProver_top ),
% 2.97/0.99      inference(renaming,[status(thm)],[c_5433]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1,plain,
% 2.97/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.97/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1925,plain,
% 2.97/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 2.97/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_5441,plain,
% 2.97/0.99      ( m1_subset_1(sK3(X0,X1,sK7),sK6) = iProver_top
% 2.97/0.99      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_5434,c_1925]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_16,plain,
% 2.97/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.97/0.99      | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1)
% 2.97/0.99      | ~ v1_relat_1(X1) ),
% 2.97/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1914,plain,
% 2.97/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 2.97/0.99      | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1) = iProver_top
% 2.97/0.99      | v1_relat_1(X1) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_23,negated_conjecture,
% 2.97/0.99      ( m1_subset_1(sK9,sK6)
% 2.97/0.99      | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) ),
% 2.97/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1908,plain,
% 2.97/0.99      ( m1_subset_1(sK9,sK6) = iProver_top
% 2.97/0.99      | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_20,negated_conjecture,
% 2.97/0.99      ( ~ m1_subset_1(X0,sK6)
% 2.97/0.99      | ~ r2_hidden(X0,sK5)
% 2.97/0.99      | ~ r2_hidden(k4_tarski(X0,sK8),sK7)
% 2.97/0.99      | ~ r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) ),
% 2.97/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1911,plain,
% 2.97/0.99      ( m1_subset_1(X0,sK6) != iProver_top
% 2.97/0.99      | r2_hidden(X0,sK5) != iProver_top
% 2.97/0.99      | r2_hidden(k4_tarski(X0,sK8),sK7) != iProver_top
% 2.97/0.99      | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2153,plain,
% 2.97/0.99      ( m1_subset_1(X0,sK6) != iProver_top
% 2.97/0.99      | m1_subset_1(sK9,sK6) = iProver_top
% 2.97/0.99      | r2_hidden(X0,sK5) != iProver_top
% 2.97/0.99      | r2_hidden(k4_tarski(X0,sK8),sK7) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_1908,c_1911]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3891,plain,
% 2.97/0.99      ( m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top
% 2.97/0.99      | m1_subset_1(sK9,sK6) = iProver_top
% 2.97/0.99      | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
% 2.97/0.99      | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top
% 2.97/0.99      | v1_relat_1(sK7) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_1914,c_2153]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4281,plain,
% 2.97/0.99      ( r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top
% 2.97/0.99      | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
% 2.97/0.99      | m1_subset_1(sK9,sK6) = iProver_top
% 2.97/0.99      | m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_3891,c_26,c_2104,c_2379,c_2571]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4282,plain,
% 2.97/0.99      ( m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top
% 2.97/0.99      | m1_subset_1(sK9,sK6) = iProver_top
% 2.97/0.99      | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
% 2.97/0.99      | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top ),
% 2.97/0.99      inference(renaming,[status(thm)],[c_4281]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_5694,plain,
% 2.97/0.99      ( m1_subset_1(sK9,sK6) = iProver_top
% 2.97/0.99      | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
% 2.97/0.99      | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_5441,c_4282]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_19,plain,
% 2.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.97/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1912,plain,
% 2.97/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.97/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3201,plain,
% 2.97/0.99      ( k7_relset_1(sK6,sK4,sK7,X0) = k9_relat_1(sK7,X0) ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_1906,c_1912]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3415,plain,
% 2.97/0.99      ( m1_subset_1(X0,sK6) != iProver_top
% 2.97/0.99      | r2_hidden(X0,sK5) != iProver_top
% 2.97/0.99      | r2_hidden(k4_tarski(X0,sK8),sK7) != iProver_top
% 2.97/0.99      | r2_hidden(sK8,k9_relat_1(sK7,sK5)) != iProver_top ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_3201,c_1911]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3888,plain,
% 2.97/0.99      ( m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top
% 2.97/0.99      | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
% 2.97/0.99      | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top
% 2.97/0.99      | r2_hidden(sK8,k9_relat_1(sK7,sK5)) != iProver_top
% 2.97/0.99      | v1_relat_1(sK7) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_1914,c_3415]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4495,plain,
% 2.97/0.99      ( r2_hidden(sK8,k9_relat_1(sK7,sK5)) != iProver_top
% 2.97/0.99      | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top
% 2.97/0.99      | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
% 2.97/0.99      | m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_3888,c_26,c_2104,c_2379,c_2571]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4496,plain,
% 2.97/0.99      ( m1_subset_1(sK3(sK8,X0,sK7),sK6) != iProver_top
% 2.97/0.99      | r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
% 2.97/0.99      | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top
% 2.97/0.99      | r2_hidden(sK8,k9_relat_1(sK7,sK5)) != iProver_top ),
% 2.97/0.99      inference(renaming,[status(thm)],[c_4495]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_5692,plain,
% 2.97/0.99      ( r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
% 2.97/0.99      | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top
% 2.97/0.99      | r2_hidden(sK8,k9_relat_1(sK7,sK5)) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_5441,c_4496]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_22,negated_conjecture,
% 2.97/0.99      ( r2_hidden(k4_tarski(sK9,sK8),sK7)
% 2.97/0.99      | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) ),
% 2.97/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1909,plain,
% 2.97/0.99      ( r2_hidden(k4_tarski(sK9,sK8),sK7) = iProver_top
% 2.97/0.99      | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3412,plain,
% 2.97/0.99      ( r2_hidden(k4_tarski(sK9,sK8),sK7) = iProver_top
% 2.97/0.99      | r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_3201,c_1909]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_8,plain,
% 2.97/0.99      ( ~ r2_hidden(X0,X1)
% 2.97/0.99      | r2_hidden(X2,k9_relat_1(X3,X1))
% 2.97/0.99      | ~ r2_hidden(k4_tarski(X0,X2),X3)
% 2.97/0.99      | ~ v1_relat_1(X3) ),
% 2.97/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1919,plain,
% 2.97/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.97/0.99      | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
% 2.97/0.99      | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
% 2.97/0.99      | v1_relat_1(X3) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4073,plain,
% 2.97/0.99      ( r2_hidden(sK9,X0) != iProver_top
% 2.97/0.99      | r2_hidden(sK8,k9_relat_1(sK7,X0)) = iProver_top
% 2.97/0.99      | r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top
% 2.97/0.99      | v1_relat_1(sK7) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_3412,c_1919]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_5336,plain,
% 2.97/0.99      ( r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top
% 2.97/0.99      | r2_hidden(sK8,k9_relat_1(sK7,X0)) = iProver_top
% 2.97/0.99      | r2_hidden(sK9,X0) != iProver_top ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_4073,c_26,c_2104,c_2379,c_2571]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_5337,plain,
% 2.97/0.99      ( r2_hidden(sK9,X0) != iProver_top
% 2.97/0.99      | r2_hidden(sK8,k9_relat_1(sK7,X0)) = iProver_top
% 2.97/0.99      | r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top ),
% 2.97/0.99      inference(renaming,[status(thm)],[c_5336]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_5346,plain,
% 2.97/0.99      ( m1_subset_1(sK8,k9_relat_1(sK7,X0)) = iProver_top
% 2.97/0.99      | r2_hidden(sK9,X0) != iProver_top
% 2.97/0.99      | r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_5337,c_1925]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_21,negated_conjecture,
% 2.97/0.99      ( r2_hidden(sK9,sK5)
% 2.97/0.99      | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) ),
% 2.97/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1910,plain,
% 2.97/0.99      ( r2_hidden(sK9,sK5) = iProver_top
% 2.97/0.99      | r2_hidden(sK8,k7_relset_1(sK6,sK4,sK7,sK5)) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3413,plain,
% 2.97/0.99      ( r2_hidden(sK9,sK5) = iProver_top
% 2.97/0.99      | r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_3201,c_1910]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_5347,plain,
% 2.97/0.99      ( r2_hidden(sK9,sK5) != iProver_top
% 2.97/0.99      | r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top
% 2.97/0.99      | iProver_top != iProver_top ),
% 2.97/0.99      inference(equality_factoring,[status(thm)],[c_5337]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_5349,plain,
% 2.97/0.99      ( r2_hidden(sK9,sK5) != iProver_top
% 2.97/0.99      | r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top ),
% 2.97/0.99      inference(equality_resolution_simp,[status(thm)],[c_5347]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_5903,plain,
% 2.97/0.99      ( r2_hidden(sK8,k9_relat_1(sK7,sK5)) = iProver_top ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_5346,c_3413,c_5349]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_6094,plain,
% 2.97/0.99      ( r2_hidden(sK3(sK8,X0,sK7),sK5) != iProver_top
% 2.97/0.99      | r2_hidden(sK8,k9_relat_1(sK7,X0)) != iProver_top ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_5694,c_3413,c_5349,c_5692]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_6102,plain,
% 2.97/0.99      ( r2_hidden(sK8,k9_relat_1(sK7,sK5)) != iProver_top
% 2.97/0.99      | v1_relat_1(sK7) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_1915,c_6094]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(contradiction,plain,
% 2.97/0.99      ( $false ),
% 2.97/0.99      inference(minisat,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_6102,c_5903,c_2571,c_2379,c_2104,c_26]) ).
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  ------                               Statistics
% 2.97/0.99  
% 2.97/0.99  ------ General
% 2.97/0.99  
% 2.97/0.99  abstr_ref_over_cycles:                  0
% 2.97/0.99  abstr_ref_under_cycles:                 0
% 2.97/0.99  gc_basic_clause_elim:                   0
% 2.97/0.99  forced_gc_time:                         0
% 2.97/0.99  parsing_time:                           0.008
% 2.97/0.99  unif_index_cands_time:                  0.
% 2.97/0.99  unif_index_add_time:                    0.
% 2.97/0.99  orderings_time:                         0.
% 2.97/0.99  out_proof_time:                         0.008
% 2.97/0.99  total_time:                             0.225
% 2.97/0.99  num_of_symbols:                         52
% 2.97/0.99  num_of_terms:                           8301
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing
% 2.97/0.99  
% 2.97/0.99  num_of_splits:                          0
% 2.97/0.99  num_of_split_atoms:                     0
% 2.97/0.99  num_of_reused_defs:                     0
% 2.97/0.99  num_eq_ax_congr_red:                    50
% 2.97/0.99  num_of_sem_filtered_clauses:            1
% 2.97/0.99  num_of_subtypes:                        0
% 2.97/0.99  monotx_restored_types:                  0
% 2.97/0.99  sat_num_of_epr_types:                   0
% 2.97/0.99  sat_num_of_non_cyclic_types:            0
% 2.97/0.99  sat_guarded_non_collapsed_types:        0
% 2.97/0.99  num_pure_diseq_elim:                    0
% 2.97/0.99  simp_replaced_by:                       0
% 2.97/0.99  res_preprocessed:                       115
% 2.97/0.99  prep_upred:                             0
% 2.97/0.99  prep_unflattend:                        58
% 2.97/0.99  smt_new_axioms:                         0
% 2.97/0.99  pred_elim_cands:                        4
% 2.97/0.99  pred_elim:                              1
% 2.97/0.99  pred_elim_cl:                           2
% 2.97/0.99  pred_elim_cycles:                       5
% 2.97/0.99  merged_defs:                            8
% 2.97/0.99  merged_defs_ncl:                        0
% 2.97/0.99  bin_hyper_res:                          10
% 2.97/0.99  prep_cycles:                            4
% 2.97/0.99  pred_elim_time:                         0.013
% 2.97/0.99  splitting_time:                         0.
% 2.97/0.99  sem_filter_time:                        0.
% 2.97/0.99  monotx_time:                            0.
% 2.97/0.99  subtype_inf_time:                       0.
% 2.97/0.99  
% 2.97/0.99  ------ Problem properties
% 2.97/0.99  
% 2.97/0.99  clauses:                                23
% 2.97/0.99  conjectures:                            6
% 2.97/0.99  epr:                                    4
% 2.97/0.99  horn:                                   18
% 2.97/0.99  ground:                                 5
% 2.97/0.99  unary:                                  3
% 2.97/0.99  binary:                                 7
% 2.97/0.99  lits:                                   62
% 2.97/0.99  lits_eq:                                4
% 2.97/0.99  fd_pure:                                0
% 2.97/0.99  fd_pseudo:                              0
% 2.97/0.99  fd_cond:                                0
% 2.97/0.99  fd_pseudo_cond:                         3
% 2.97/0.99  ac_symbols:                             0
% 2.97/0.99  
% 2.97/0.99  ------ Propositional Solver
% 2.97/0.99  
% 2.97/0.99  prop_solver_calls:                      27
% 2.97/0.99  prop_fast_solver_calls:                 1018
% 2.97/0.99  smt_solver_calls:                       0
% 2.97/0.99  smt_fast_solver_calls:                  0
% 2.97/0.99  prop_num_of_clauses:                    2310
% 2.97/0.99  prop_preprocess_simplified:             5716
% 2.97/0.99  prop_fo_subsumed:                       16
% 2.97/0.99  prop_solver_time:                       0.
% 2.97/0.99  smt_solver_time:                        0.
% 2.97/0.99  smt_fast_solver_time:                   0.
% 2.97/0.99  prop_fast_solver_time:                  0.
% 2.97/0.99  prop_unsat_core_time:                   0.
% 2.97/0.99  
% 2.97/0.99  ------ QBF
% 2.97/0.99  
% 2.97/0.99  qbf_q_res:                              0
% 2.97/0.99  qbf_num_tautologies:                    0
% 2.97/0.99  qbf_prep_cycles:                        0
% 2.97/0.99  
% 2.97/0.99  ------ BMC1
% 2.97/0.99  
% 2.97/0.99  bmc1_current_bound:                     -1
% 2.97/0.99  bmc1_last_solved_bound:                 -1
% 2.97/0.99  bmc1_unsat_core_size:                   -1
% 2.97/0.99  bmc1_unsat_core_parents_size:           -1
% 2.97/0.99  bmc1_merge_next_fun:                    0
% 2.97/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.97/0.99  
% 2.97/0.99  ------ Instantiation
% 2.97/0.99  
% 2.97/0.99  inst_num_of_clauses:                    546
% 2.97/0.99  inst_num_in_passive:                    4
% 2.97/0.99  inst_num_in_active:                     278
% 2.97/0.99  inst_num_in_unprocessed:                264
% 2.97/0.99  inst_num_of_loops:                      330
% 2.97/0.99  inst_num_of_learning_restarts:          0
% 2.97/0.99  inst_num_moves_active_passive:          49
% 2.97/0.99  inst_lit_activity:                      0
% 2.97/0.99  inst_lit_activity_moves:                0
% 2.97/0.99  inst_num_tautologies:                   0
% 2.97/0.99  inst_num_prop_implied:                  0
% 2.97/0.99  inst_num_existing_simplified:           0
% 2.97/0.99  inst_num_eq_res_simplified:             0
% 2.97/0.99  inst_num_child_elim:                    0
% 2.97/0.99  inst_num_of_dismatching_blockings:      100
% 2.97/0.99  inst_num_of_non_proper_insts:           371
% 2.97/0.99  inst_num_of_duplicates:                 0
% 2.97/0.99  inst_inst_num_from_inst_to_res:         0
% 2.97/0.99  inst_dismatching_checking_time:         0.
% 2.97/0.99  
% 2.97/0.99  ------ Resolution
% 2.97/0.99  
% 2.97/0.99  res_num_of_clauses:                     0
% 2.97/0.99  res_num_in_passive:                     0
% 2.97/0.99  res_num_in_active:                      0
% 2.97/0.99  res_num_of_loops:                       119
% 2.97/0.99  res_forward_subset_subsumed:            28
% 2.97/0.99  res_backward_subset_subsumed:           0
% 2.97/0.99  res_forward_subsumed:                   0
% 2.97/0.99  res_backward_subsumed:                  0
% 2.97/0.99  res_forward_subsumption_resolution:     0
% 2.97/0.99  res_backward_subsumption_resolution:    0
% 2.97/0.99  res_clause_to_clause_subsumption:       221
% 2.97/0.99  res_orphan_elimination:                 0
% 2.97/0.99  res_tautology_del:                      56
% 2.97/0.99  res_num_eq_res_simplified:              0
% 2.97/0.99  res_num_sel_changes:                    0
% 2.97/0.99  res_moves_from_active_to_pass:          0
% 2.97/0.99  
% 2.97/0.99  ------ Superposition
% 2.97/0.99  
% 2.97/0.99  sup_time_total:                         0.
% 2.97/0.99  sup_time_generating:                    0.
% 2.97/0.99  sup_time_sim_full:                      0.
% 2.97/0.99  sup_time_sim_immed:                     0.
% 2.97/0.99  
% 2.97/0.99  sup_num_of_clauses:                     91
% 2.97/0.99  sup_num_in_active:                      56
% 2.97/0.99  sup_num_in_passive:                     35
% 2.97/0.99  sup_num_of_loops:                       65
% 2.97/0.99  sup_fw_superposition:                   25
% 2.97/0.99  sup_bw_superposition:                   56
% 2.97/0.99  sup_immediate_simplified:               1
% 2.97/0.99  sup_given_eliminated:                   0
% 2.97/0.99  comparisons_done:                       0
% 2.97/0.99  comparisons_avoided:                    0
% 2.97/0.99  
% 2.97/0.99  ------ Simplifications
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  sim_fw_subset_subsumed:                 0
% 2.97/0.99  sim_bw_subset_subsumed:                 4
% 2.97/0.99  sim_fw_subsumed:                        1
% 2.97/0.99  sim_bw_subsumed:                        0
% 2.97/0.99  sim_fw_subsumption_res:                 0
% 2.97/0.99  sim_bw_subsumption_res:                 0
% 2.97/0.99  sim_tautology_del:                      5
% 2.97/0.99  sim_eq_tautology_del:                   0
% 2.97/0.99  sim_eq_res_simp:                        1
% 2.97/0.99  sim_fw_demodulated:                     0
% 2.97/0.99  sim_bw_demodulated:                     7
% 2.97/0.99  sim_light_normalised:                   0
% 2.97/0.99  sim_joinable_taut:                      0
% 2.97/0.99  sim_joinable_simp:                      0
% 2.97/0.99  sim_ac_normalised:                      0
% 2.97/0.99  sim_smt_subsumption:                    0
% 2.97/0.99  
%------------------------------------------------------------------------------
