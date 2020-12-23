%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:57:08 EST 2020

% Result     : Theorem 7.77s
% Output     : CNFRefutation 7.77s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 826 expanded)
%              Number of clauses        :   86 ( 257 expanded)
%              Number of leaves         :   17 ( 206 expanded)
%              Depth                    :   21
%              Number of atoms          :  502 (4146 expanded)
%              Number of equality atoms :  182 ( 883 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( r2_relset_1(X0,X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,X0)
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r2_hidden(k4_tarski(X4,X5),X2)
                    <=> r2_hidden(k4_tarski(X4,X5),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_relset_1(X0,X1,X2,X3)
          <=> ! [X4] :
                ( ! [X5] :
                    ( ( r2_hidden(k4_tarski(X4,X5),X2)
                    <=> r2_hidden(k4_tarski(X4,X5),X3) )
                    | ~ m1_subset_1(X5,X1) )
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_relset_1(X0,X1,X2,X3)
              | ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                        | ~ r2_hidden(k4_tarski(X4,X5),X2) )
                      & ( r2_hidden(k4_tarski(X4,X5),X3)
                        | r2_hidden(k4_tarski(X4,X5),X2) )
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( ( ( r2_hidden(k4_tarski(X4,X5),X2)
                          | ~ r2_hidden(k4_tarski(X4,X5),X3) )
                        & ( r2_hidden(k4_tarski(X4,X5),X3)
                          | ~ r2_hidden(k4_tarski(X4,X5),X2) ) )
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,X0) )
              | ~ r2_relset_1(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_relset_1(X0,X1,X2,X3)
              | ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                        | ~ r2_hidden(k4_tarski(X4,X5),X2) )
                      & ( r2_hidden(k4_tarski(X4,X5),X3)
                        | r2_hidden(k4_tarski(X4,X5),X2) )
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( ( ( r2_hidden(k4_tarski(X4,X5),X2)
                          | ~ r2_hidden(k4_tarski(X4,X5),X3) )
                        & ( r2_hidden(k4_tarski(X4,X5),X3)
                          | ~ r2_hidden(k4_tarski(X4,X5),X2) ) )
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,X0) )
              | ~ r2_relset_1(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_relset_1(X0,X1,X2,X3)
              | ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                        | ~ r2_hidden(k4_tarski(X4,X5),X2) )
                      & ( r2_hidden(k4_tarski(X4,X5),X3)
                        | r2_hidden(k4_tarski(X4,X5),X2) )
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X6] :
                  ( ! [X7] :
                      ( ( ( r2_hidden(k4_tarski(X6,X7),X2)
                          | ~ r2_hidden(k4_tarski(X6,X7),X3) )
                        & ( r2_hidden(k4_tarski(X6,X7),X3)
                          | ~ r2_hidden(k4_tarski(X6,X7),X2) ) )
                      | ~ m1_subset_1(X7,X1) )
                  | ~ m1_subset_1(X6,X0) )
              | ~ r2_relset_1(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f24])).

fof(f27,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
            | ~ r2_hidden(k4_tarski(X4,X5),X2) )
          & ( r2_hidden(k4_tarski(X4,X5),X3)
            | r2_hidden(k4_tarski(X4,X5),X2) )
          & m1_subset_1(X5,X1) )
     => ( ( ~ r2_hidden(k4_tarski(X4,sK1(X0,X1,X2,X3)),X3)
          | ~ r2_hidden(k4_tarski(X4,sK1(X0,X1,X2,X3)),X2) )
        & ( r2_hidden(k4_tarski(X4,sK1(X0,X1,X2,X3)),X3)
          | r2_hidden(k4_tarski(X4,sK1(X0,X1,X2,X3)),X2) )
        & m1_subset_1(sK1(X0,X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ~ r2_hidden(k4_tarski(X4,X5),X3)
                | ~ r2_hidden(k4_tarski(X4,X5),X2) )
              & ( r2_hidden(k4_tarski(X4,X5),X3)
                | r2_hidden(k4_tarski(X4,X5),X2) )
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,X0) )
     => ( ? [X5] :
            ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),X5),X3)
              | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),X5),X2) )
            & ( r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),X5),X3)
              | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),X5),X2) )
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK0(X0,X1,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_relset_1(X0,X1,X2,X3)
              | ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3)
                  | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2) )
                & ( r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3)
                  | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2) )
                & m1_subset_1(sK1(X0,X1,X2,X3),X1)
                & m1_subset_1(sK0(X0,X1,X2,X3),X0) ) )
            & ( ! [X6] :
                  ( ! [X7] :
                      ( ( ( r2_hidden(k4_tarski(X6,X7),X2)
                          | ~ r2_hidden(k4_tarski(X6,X7),X3) )
                        & ( r2_hidden(k4_tarski(X6,X7),X3)
                          | ~ r2_hidden(k4_tarski(X6,X7),X2) ) )
                      | ~ m1_subset_1(X7,X1) )
                  | ~ m1_subset_1(X6,X0) )
              | ~ r2_relset_1(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f27,f26])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3)
      | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
         => ( ! [X3] :
                ( r2_hidden(X3,X0)
               => k11_relat_1(X1,X3) = k11_relat_1(X2,X3) )
           => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
           => ( ! [X3] :
                  ( r2_hidden(X3,X0)
                 => k11_relat_1(X1,X3) = k11_relat_1(X2,X3) )
             => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & ! [X3] :
              ( k11_relat_1(X1,X3) = k11_relat_1(X2,X3)
              | ~ r2_hidden(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & ! [X3] :
              ( k11_relat_1(X1,X3) = k11_relat_1(X2,X3)
              | ~ r2_hidden(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f19])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & ! [X3] :
              ( k11_relat_1(X1,X3) = k11_relat_1(X2,X3)
              | ~ r2_hidden(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
     => ( ~ r2_relset_1(X0,X0,X1,sK4)
        & ! [X3] :
            ( k11_relat_1(sK4,X3) = k11_relat_1(X1,X3)
            | ~ r2_hidden(X3,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X1,X2)
            & ! [X3] :
                ( k11_relat_1(X1,X3) = k11_relat_1(X2,X3)
                | ~ r2_hidden(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK2,sK2,sK3,X2)
          & ! [X3] :
              ( k11_relat_1(sK3,X3) = k11_relat_1(X2,X3)
              | ~ r2_hidden(X3,sK2) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ r2_relset_1(sK2,sK2,sK3,sK4)
    & ! [X3] :
        ( k11_relat_1(sK3,X3) = k11_relat_1(sK4,X3)
        | ~ r2_hidden(X3,sK2) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f31,f30])).

fof(f52,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | m1_subset_1(sK0(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    ! [X3] :
      ( k11_relat_1(sK3,X3) = k11_relat_1(sK4,X3)
      | ~ r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    ~ r2_relset_1(sK2,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | m1_subset_1(sK1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f17])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f50])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3)
      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_11,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1082,plain,
    ( r2_relset_1(X0,X1,X2,X3) = iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) = iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1085,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3602,plain,
    ( r2_relset_1(X0,X1,X2,X3) = iProver_top
    | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X2,sK0(X0,X1,X2,X3))) = iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1082,c_1085])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1073,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1072,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_13,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(sK0(X0,X1,X2,X3),X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1080,plain,
    ( r2_relset_1(X0,X1,X2,X3) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(sK0(X0,X1,X2,X3),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1089,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3131,plain,
    ( r2_relset_1(X0,X1,X2,X3) = iProver_top
    | r2_hidden(sK0(X0,X1,X2,X3),X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1080,c_1089])).

cnf(c_19,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | k11_relat_1(sK3,X0) = k11_relat_1(sK4,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1074,plain,
    ( k11_relat_1(sK3,X0) = k11_relat_1(sK4,X0)
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7868,plain,
    ( k11_relat_1(sK4,sK0(sK2,X0,X1,X2)) = k11_relat_1(sK3,sK0(sK2,X0,X1,X2))
    | r2_relset_1(sK2,X0,X1,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3131,c_1074])).

cnf(c_8816,plain,
    ( k11_relat_1(sK3,sK0(sK2,sK2,sK3,X0)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,X0))
    | r2_relset_1(sK2,sK2,sK3,X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1072,c_7868])).

cnf(c_9423,plain,
    ( k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))
    | r2_relset_1(sK2,sK2,sK3,sK4) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1073,c_8816])).

cnf(c_18,negated_conjecture,
    ( ~ r2_relset_1(sK2,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_27,plain,
    ( r2_relset_1(sK2,sK2,sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9576,plain,
    ( k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))
    | v1_xboole_0(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9423,c_27])).

cnf(c_12,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(sK1(X0,X1,X2,X3),X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1081,plain,
    ( r2_relset_1(X0,X1,X2,X3) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(sK1(X0,X1,X2,X3),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1091,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3406,plain,
    ( r2_relset_1(X0,X1,X2,X3) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(sK1(X0,X1,X2,X3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1081,c_1091])).

cnf(c_7905,plain,
    ( r2_relset_1(sK2,sK2,sK3,X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_xboole_0(sK1(sK2,sK2,sK3,X0)) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1072,c_3406])).

cnf(c_8613,plain,
    ( r2_relset_1(sK2,sK2,sK3,sK4) = iProver_top
    | v1_xboole_0(sK1(sK2,sK2,sK3,sK4)) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1073,c_7905])).

cnf(c_8706,plain,
    ( v1_xboole_0(sK1(sK2,sK2,sK3,sK4)) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8613,c_27])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1093,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8712,plain,
    ( sK1(sK2,sK2,sK3,sK4) = k1_xboole_0
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8706,c_1093])).

cnf(c_9583,plain,
    ( sK1(sK2,sK2,sK3,sK4) = k1_xboole_0
    | k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_9576,c_8712])).

cnf(c_669,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | r2_relset_1(X4,X5,X6,X7)
    | X4 != X0
    | X5 != X1
    | X6 != X2
    | X7 != X3 ),
    theory(equality)).

cnf(c_16,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1743,plain,
    ( r2_relset_1(sK2,sK2,sK3,sK3) ),
    inference(resolution,[status(thm)],[c_16,c_21])).

cnf(c_3736,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | X2 != sK3
    | X3 != sK3
    | X0 != sK2
    | X1 != sK2 ),
    inference(resolution,[status(thm)],[c_669,c_1743])).

cnf(c_4623,plain,
    ( sK4 != sK3
    | sK3 != sK3
    | sK2 != sK2 ),
    inference(resolution,[status(thm)],[c_3736,c_18])).

cnf(c_4624,plain,
    ( sK4 != sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_4623])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1084,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2435,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1072,c_1084])).

cnf(c_9587,plain,
    ( k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_9576,c_2435])).

cnf(c_10055,plain,
    ( k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9587,c_1093])).

cnf(c_2434,plain,
    ( v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1073,c_1084])).

cnf(c_9588,plain,
    ( k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_9576,c_2434])).

cnf(c_10059,plain,
    ( k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9588,c_1093])).

cnf(c_661,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1537,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_661])).

cnf(c_7317,plain,
    ( X0 = sK3
    | X0 != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1537])).

cnf(c_10804,plain,
    ( sK4 = sK3
    | sK4 != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7317])).

cnf(c_10861,plain,
    ( k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9583,c_4624,c_10055,c_10059,c_10804])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1086,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_10864,plain,
    ( r2_hidden(X0,k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),X0),sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_10861,c_1086])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_47,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_49,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1504,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK2))
    | v1_relat_1(sK4) ),
    inference(resolution,[status(thm)],[c_5,c_20])).

cnf(c_1505,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1504])).

cnf(c_11276,plain,
    ( r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),X0),sK4) = iProver_top
    | r2_hidden(X0,k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10864,c_49,c_1505])).

cnf(c_11277,plain,
    ( r2_hidden(X0,k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),X0),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_11276])).

cnf(c_24438,plain,
    ( r2_relset_1(sK2,sK2,sK3,sK4) = iProver_top
    | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3602,c_11277])).

cnf(c_663,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2942,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4)))
    | X0 != sK1(sK2,sK2,sK3,sK4)
    | X1 != k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_663])).

cnf(c_8588,plain,
    ( r2_hidden(sK1(sK2,sK2,sK3,sK4),X0)
    | ~ r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4)))
    | X0 != k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))
    | sK1(sK2,sK2,sK3,sK4) != sK1(sK2,sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2942])).

cnf(c_13437,plain,
    ( ~ r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4)))
    | r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)))
    | sK1(sK2,sK2,sK3,sK4) != sK1(sK2,sK2,sK3,sK4)
    | k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) != k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_8588])).

cnf(c_13438,plain,
    ( sK1(sK2,sK2,sK3,sK4) != sK1(sK2,sK2,sK3,sK4)
    | k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) != k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))
    | r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))) != iProver_top
    | r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13437])).

cnf(c_4640,plain,
    ( ~ r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)))
    | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_4641,plain,
    ( r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4640])).

cnf(c_660,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2094,plain,
    ( sK1(sK2,sK2,sK3,sK4) = sK1(sK2,sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_660])).

cnf(c_1872,plain,
    ( r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4)))
    | ~ r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1873,plain,
    ( r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))) = iProver_top
    | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1872])).

cnf(c_1506,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK2))
    | v1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_5,c_21])).

cnf(c_1507,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1506])).

cnf(c_10,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3)
    | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_552,plain,
    ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3)
    | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | sK4 != X3
    | sK3 != X2
    | sK2 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_18])).

cnf(c_553,plain,
    ( ~ r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4)
    | ~ r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(unflattening,[status(thm)],[c_552])).

cnf(c_555,plain,
    ( ~ r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4)
    | ~ r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_553,c_21,c_20])).

cnf(c_557,plain,
    ( r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_555])).

cnf(c_23,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_22,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_24438,c_13438,c_10861,c_4641,c_2094,c_1873,c_1507,c_1505,c_557,c_49,c_27,c_23,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:56:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.77/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.77/1.50  
% 7.77/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.77/1.50  
% 7.77/1.50  ------  iProver source info
% 7.77/1.50  
% 7.77/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.77/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.77/1.50  git: non_committed_changes: false
% 7.77/1.50  git: last_make_outside_of_git: false
% 7.77/1.50  
% 7.77/1.50  ------ 
% 7.77/1.50  ------ Parsing...
% 7.77/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.77/1.50  
% 7.77/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.77/1.50  
% 7.77/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.77/1.50  
% 7.77/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.77/1.50  ------ Proving...
% 7.77/1.50  ------ Problem Properties 
% 7.77/1.50  
% 7.77/1.50  
% 7.77/1.50  clauses                                 22
% 7.77/1.50  conjectures                             4
% 7.77/1.50  EPR                                     6
% 7.77/1.50  Horn                                    17
% 7.77/1.50  unary                                   4
% 7.77/1.50  binary                                  3
% 7.77/1.50  lits                                    70
% 7.77/1.50  lits eq                                 3
% 7.77/1.50  fd_pure                                 0
% 7.77/1.50  fd_pseudo                               0
% 7.77/1.50  fd_cond                                 1
% 7.77/1.50  fd_pseudo_cond                          1
% 7.77/1.50  AC symbols                              0
% 7.77/1.50  
% 7.77/1.50  ------ Input Options Time Limit: Unbounded
% 7.77/1.50  
% 7.77/1.50  
% 7.77/1.50  ------ 
% 7.77/1.50  Current options:
% 7.77/1.50  ------ 
% 7.77/1.50  
% 7.77/1.50  
% 7.77/1.50  
% 7.77/1.50  
% 7.77/1.50  ------ Proving...
% 7.77/1.50  
% 7.77/1.50  
% 7.77/1.50  % SZS status Theorem for theBenchmark.p
% 7.77/1.50  
% 7.77/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.77/1.50  
% 7.77/1.50  fof(f7,axiom,(
% 7.77/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => (r2_hidden(k4_tarski(X4,X5),X2) <=> r2_hidden(k4_tarski(X4,X5),X3)))))))),
% 7.77/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.77/1.50  
% 7.77/1.50  fof(f16,plain,(
% 7.77/1.50    ! [X0,X1,X2] : (! [X3] : ((r2_relset_1(X0,X1,X2,X3) <=> ! [X4] : (! [X5] : ((r2_hidden(k4_tarski(X4,X5),X2) <=> r2_hidden(k4_tarski(X4,X5),X3)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.77/1.50    inference(ennf_transformation,[],[f7])).
% 7.77/1.50  
% 7.77/1.50  fof(f23,plain,(
% 7.77/1.50    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : (((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2))) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X4] : (! [X5] : (((r2_hidden(k4_tarski(X4,X5),X2) | ~r2_hidden(k4_tarski(X4,X5),X3)) & (r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2))) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.77/1.50    inference(nnf_transformation,[],[f16])).
% 7.77/1.50  
% 7.77/1.50  fof(f24,plain,(
% 7.77/1.50    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X4] : (! [X5] : (((r2_hidden(k4_tarski(X4,X5),X2) | ~r2_hidden(k4_tarski(X4,X5),X3)) & (r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2))) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.77/1.50    inference(flattening,[],[f23])).
% 7.77/1.50  
% 7.77/1.50  fof(f25,plain,(
% 7.77/1.50    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0))) & (! [X6] : (! [X7] : (((r2_hidden(k4_tarski(X6,X7),X2) | ~r2_hidden(k4_tarski(X6,X7),X3)) & (r2_hidden(k4_tarski(X6,X7),X3) | ~r2_hidden(k4_tarski(X6,X7),X2))) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.77/1.50    inference(rectify,[],[f24])).
% 7.77/1.50  
% 7.77/1.50  fof(f27,plain,(
% 7.77/1.50    ( ! [X4] : (! [X3,X2,X1,X0] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) => ((~r2_hidden(k4_tarski(X4,sK1(X0,X1,X2,X3)),X3) | ~r2_hidden(k4_tarski(X4,sK1(X0,X1,X2,X3)),X2)) & (r2_hidden(k4_tarski(X4,sK1(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(X4,sK1(X0,X1,X2,X3)),X2)) & m1_subset_1(sK1(X0,X1,X2,X3),X1)))) )),
% 7.77/1.50    introduced(choice_axiom,[])).
% 7.77/1.50  
% 7.77/1.50  fof(f26,plain,(
% 7.77/1.50    ! [X3,X2,X1,X0] : (? [X4] : (? [X5] : ((~r2_hidden(k4_tarski(X4,X5),X3) | ~r2_hidden(k4_tarski(X4,X5),X2)) & (r2_hidden(k4_tarski(X4,X5),X3) | r2_hidden(k4_tarski(X4,X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) => (? [X5] : ((~r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),X5),X3) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),X5),X2)) & (r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),X5),X3) | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),X5),X2)) & m1_subset_1(X5,X1)) & m1_subset_1(sK0(X0,X1,X2,X3),X0)))),
% 7.77/1.50    introduced(choice_axiom,[])).
% 7.77/1.50  
% 7.77/1.50  fof(f28,plain,(
% 7.77/1.50    ! [X0,X1,X2] : (! [X3] : (((r2_relset_1(X0,X1,X2,X3) | (((~r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2)) & (r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2)) & m1_subset_1(sK1(X0,X1,X2,X3),X1)) & m1_subset_1(sK0(X0,X1,X2,X3),X0))) & (! [X6] : (! [X7] : (((r2_hidden(k4_tarski(X6,X7),X2) | ~r2_hidden(k4_tarski(X6,X7),X3)) & (r2_hidden(k4_tarski(X6,X7),X3) | ~r2_hidden(k4_tarski(X6,X7),X2))) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.77/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f27,f26])).
% 7.77/1.50  
% 7.77/1.50  fof(f47,plain,(
% 7.77/1.50    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.77/1.50    inference(cnf_transformation,[],[f28])).
% 7.77/1.50  
% 7.77/1.50  fof(f5,axiom,(
% 7.77/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 7.77/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.77/1.50  
% 7.77/1.50  fof(f14,plain,(
% 7.77/1.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 7.77/1.50    inference(ennf_transformation,[],[f5])).
% 7.77/1.50  
% 7.77/1.50  fof(f22,plain,(
% 7.77/1.50    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 7.77/1.50    inference(nnf_transformation,[],[f14])).
% 7.77/1.50  
% 7.77/1.50  fof(f40,plain,(
% 7.77/1.50    ( ! [X2,X0,X1] : (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 7.77/1.50    inference(cnf_transformation,[],[f22])).
% 7.77/1.50  
% 7.77/1.50  fof(f9,conjecture,(
% 7.77/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (! [X3] : (r2_hidden(X3,X0) => k11_relat_1(X1,X3) = k11_relat_1(X2,X3)) => r2_relset_1(X0,X0,X1,X2))))),
% 7.77/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.77/1.50  
% 7.77/1.50  fof(f10,negated_conjecture,(
% 7.77/1.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (! [X3] : (r2_hidden(X3,X0) => k11_relat_1(X1,X3) = k11_relat_1(X2,X3)) => r2_relset_1(X0,X0,X1,X2))))),
% 7.77/1.50    inference(negated_conjecture,[],[f9])).
% 7.77/1.50  
% 7.77/1.50  fof(f19,plain,(
% 7.77/1.50    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X1,X2) & ! [X3] : (k11_relat_1(X1,X3) = k11_relat_1(X2,X3) | ~r2_hidden(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 7.77/1.50    inference(ennf_transformation,[],[f10])).
% 7.77/1.50  
% 7.77/1.50  fof(f20,plain,(
% 7.77/1.50    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X1,X2) & ! [X3] : (k11_relat_1(X1,X3) = k11_relat_1(X2,X3) | ~r2_hidden(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 7.77/1.50    inference(flattening,[],[f19])).
% 7.77/1.50  
% 7.77/1.50  fof(f31,plain,(
% 7.77/1.50    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X1,X2) & ! [X3] : (k11_relat_1(X1,X3) = k11_relat_1(X2,X3) | ~r2_hidden(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) => (~r2_relset_1(X0,X0,X1,sK4) & ! [X3] : (k11_relat_1(sK4,X3) = k11_relat_1(X1,X3) | ~r2_hidden(X3,X0)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))) )),
% 7.77/1.50    introduced(choice_axiom,[])).
% 7.77/1.50  
% 7.77/1.50  fof(f30,plain,(
% 7.77/1.50    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X1,X2) & ! [X3] : (k11_relat_1(X1,X3) = k11_relat_1(X2,X3) | ~r2_hidden(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) => (? [X2] : (~r2_relset_1(sK2,sK2,sK3,X2) & ! [X3] : (k11_relat_1(sK3,X3) = k11_relat_1(X2,X3) | ~r2_hidden(X3,sK2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))))),
% 7.77/1.50    introduced(choice_axiom,[])).
% 7.77/1.50  
% 7.77/1.50  fof(f32,plain,(
% 7.77/1.50    (~r2_relset_1(sK2,sK2,sK3,sK4) & ! [X3] : (k11_relat_1(sK3,X3) = k11_relat_1(sK4,X3) | ~r2_hidden(X3,sK2)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 7.77/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f31,f30])).
% 7.77/1.50  
% 7.77/1.50  fof(f52,plain,(
% 7.77/1.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 7.77/1.50    inference(cnf_transformation,[],[f32])).
% 7.77/1.50  
% 7.77/1.50  fof(f51,plain,(
% 7.77/1.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 7.77/1.50    inference(cnf_transformation,[],[f32])).
% 7.77/1.50  
% 7.77/1.50  fof(f45,plain,(
% 7.77/1.50    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | m1_subset_1(sK0(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.77/1.50    inference(cnf_transformation,[],[f28])).
% 7.77/1.50  
% 7.77/1.50  fof(f2,axiom,(
% 7.77/1.50    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 7.77/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.77/1.50  
% 7.77/1.50  fof(f12,plain,(
% 7.77/1.50    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 7.77/1.50    inference(ennf_transformation,[],[f2])).
% 7.77/1.50  
% 7.77/1.50  fof(f21,plain,(
% 7.77/1.50    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 7.77/1.50    inference(nnf_transformation,[],[f12])).
% 7.77/1.50  
% 7.77/1.50  fof(f34,plain,(
% 7.77/1.50    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.77/1.50    inference(cnf_transformation,[],[f21])).
% 7.77/1.50  
% 7.77/1.50  fof(f53,plain,(
% 7.77/1.50    ( ! [X3] : (k11_relat_1(sK3,X3) = k11_relat_1(sK4,X3) | ~r2_hidden(X3,sK2)) )),
% 7.77/1.50    inference(cnf_transformation,[],[f32])).
% 7.77/1.50  
% 7.77/1.50  fof(f54,plain,(
% 7.77/1.50    ~r2_relset_1(sK2,sK2,sK3,sK4)),
% 7.77/1.50    inference(cnf_transformation,[],[f32])).
% 7.77/1.50  
% 7.77/1.50  fof(f46,plain,(
% 7.77/1.50    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | m1_subset_1(sK1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.77/1.50    inference(cnf_transformation,[],[f28])).
% 7.77/1.50  
% 7.77/1.50  fof(f36,plain,(
% 7.77/1.50    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 7.77/1.50    inference(cnf_transformation,[],[f21])).
% 7.77/1.50  
% 7.77/1.50  fof(f1,axiom,(
% 7.77/1.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.77/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.77/1.50  
% 7.77/1.50  fof(f11,plain,(
% 7.77/1.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.77/1.50    inference(ennf_transformation,[],[f1])).
% 7.77/1.50  
% 7.77/1.50  fof(f33,plain,(
% 7.77/1.50    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.77/1.50    inference(cnf_transformation,[],[f11])).
% 7.77/1.50  
% 7.77/1.50  fof(f8,axiom,(
% 7.77/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.77/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.77/1.50  
% 7.77/1.50  fof(f17,plain,(
% 7.77/1.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.77/1.50    inference(ennf_transformation,[],[f8])).
% 7.77/1.50  
% 7.77/1.50  fof(f18,plain,(
% 7.77/1.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.77/1.50    inference(flattening,[],[f17])).
% 7.77/1.50  
% 7.77/1.50  fof(f29,plain,(
% 7.77/1.50    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.77/1.50    inference(nnf_transformation,[],[f18])).
% 7.77/1.50  
% 7.77/1.50  fof(f50,plain,(
% 7.77/1.50    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.77/1.50    inference(cnf_transformation,[],[f29])).
% 7.77/1.50  
% 7.77/1.50  fof(f55,plain,(
% 7.77/1.50    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.77/1.50    inference(equality_resolution,[],[f50])).
% 7.77/1.50  
% 7.77/1.50  fof(f6,axiom,(
% 7.77/1.50    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 7.77/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.77/1.50  
% 7.77/1.50  fof(f15,plain,(
% 7.77/1.50    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 7.77/1.50    inference(ennf_transformation,[],[f6])).
% 7.77/1.50  
% 7.77/1.50  fof(f42,plain,(
% 7.77/1.50    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 7.77/1.50    inference(cnf_transformation,[],[f15])).
% 7.77/1.50  
% 7.77/1.50  fof(f41,plain,(
% 7.77/1.50    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 7.77/1.50    inference(cnf_transformation,[],[f22])).
% 7.77/1.50  
% 7.77/1.50  fof(f4,axiom,(
% 7.77/1.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.77/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.77/1.50  
% 7.77/1.50  fof(f39,plain,(
% 7.77/1.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.77/1.50    inference(cnf_transformation,[],[f4])).
% 7.77/1.50  
% 7.77/1.50  fof(f3,axiom,(
% 7.77/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.77/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.77/1.50  
% 7.77/1.50  fof(f13,plain,(
% 7.77/1.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.77/1.50    inference(ennf_transformation,[],[f3])).
% 7.77/1.50  
% 7.77/1.50  fof(f38,plain,(
% 7.77/1.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.77/1.50    inference(cnf_transformation,[],[f13])).
% 7.77/1.50  
% 7.77/1.50  fof(f48,plain,(
% 7.77/1.50    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.77/1.50    inference(cnf_transformation,[],[f28])).
% 7.77/1.50  
% 7.77/1.50  cnf(c_11,plain,
% 7.77/1.50      ( r2_relset_1(X0,X1,X2,X3)
% 7.77/1.50      | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3)
% 7.77/1.50      | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2)
% 7.77/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.77/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 7.77/1.50      inference(cnf_transformation,[],[f47]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_1082,plain,
% 7.77/1.50      ( r2_relset_1(X0,X1,X2,X3) = iProver_top
% 7.77/1.50      | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) = iProver_top
% 7.77/1.50      | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2) = iProver_top
% 7.77/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.77/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_8,plain,
% 7.77/1.50      ( r2_hidden(X0,k11_relat_1(X1,X2))
% 7.77/1.50      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 7.77/1.50      | ~ v1_relat_1(X1) ),
% 7.77/1.50      inference(cnf_transformation,[],[f40]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_1085,plain,
% 7.77/1.50      ( r2_hidden(X0,k11_relat_1(X1,X2)) = iProver_top
% 7.77/1.50      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
% 7.77/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.77/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_3602,plain,
% 7.77/1.50      ( r2_relset_1(X0,X1,X2,X3) = iProver_top
% 7.77/1.50      | r2_hidden(sK1(X0,X1,X2,X3),k11_relat_1(X2,sK0(X0,X1,X2,X3))) = iProver_top
% 7.77/1.50      | r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3) = iProver_top
% 7.77/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.50      | v1_relat_1(X2) != iProver_top ),
% 7.77/1.50      inference(superposition,[status(thm)],[c_1082,c_1085]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_20,negated_conjecture,
% 7.77/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 7.77/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_1073,plain,
% 7.77/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 7.77/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_21,negated_conjecture,
% 7.77/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 7.77/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_1072,plain,
% 7.77/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 7.77/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_13,plain,
% 7.77/1.50      ( r2_relset_1(X0,X1,X2,X3)
% 7.77/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.77/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.77/1.50      | m1_subset_1(sK0(X0,X1,X2,X3),X0) ),
% 7.77/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_1080,plain,
% 7.77/1.50      ( r2_relset_1(X0,X1,X2,X3) = iProver_top
% 7.77/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.50      | m1_subset_1(sK0(X0,X1,X2,X3),X0) = iProver_top ),
% 7.77/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_4,plain,
% 7.77/1.50      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 7.77/1.50      inference(cnf_transformation,[],[f34]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_1089,plain,
% 7.77/1.50      ( r2_hidden(X0,X1) = iProver_top
% 7.77/1.50      | m1_subset_1(X0,X1) != iProver_top
% 7.77/1.50      | v1_xboole_0(X1) = iProver_top ),
% 7.77/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_3131,plain,
% 7.77/1.50      ( r2_relset_1(X0,X1,X2,X3) = iProver_top
% 7.77/1.50      | r2_hidden(sK0(X0,X1,X2,X3),X0) = iProver_top
% 7.77/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.77/1.50      inference(superposition,[status(thm)],[c_1080,c_1089]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_19,negated_conjecture,
% 7.77/1.50      ( ~ r2_hidden(X0,sK2) | k11_relat_1(sK3,X0) = k11_relat_1(sK4,X0) ),
% 7.77/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_1074,plain,
% 7.77/1.50      ( k11_relat_1(sK3,X0) = k11_relat_1(sK4,X0)
% 7.77/1.50      | r2_hidden(X0,sK2) != iProver_top ),
% 7.77/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_7868,plain,
% 7.77/1.50      ( k11_relat_1(sK4,sK0(sK2,X0,X1,X2)) = k11_relat_1(sK3,sK0(sK2,X0,X1,X2))
% 7.77/1.50      | r2_relset_1(sK2,X0,X1,X2) = iProver_top
% 7.77/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 7.77/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 7.77/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.77/1.50      inference(superposition,[status(thm)],[c_3131,c_1074]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_8816,plain,
% 7.77/1.50      ( k11_relat_1(sK3,sK0(sK2,sK2,sK3,X0)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,X0))
% 7.77/1.50      | r2_relset_1(sK2,sK2,sK3,X0) = iProver_top
% 7.77/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 7.77/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.77/1.50      inference(superposition,[status(thm)],[c_1072,c_7868]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_9423,plain,
% 7.77/1.50      ( k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))
% 7.77/1.50      | r2_relset_1(sK2,sK2,sK3,sK4) = iProver_top
% 7.77/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.77/1.50      inference(superposition,[status(thm)],[c_1073,c_8816]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_18,negated_conjecture,
% 7.77/1.50      ( ~ r2_relset_1(sK2,sK2,sK3,sK4) ),
% 7.77/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_27,plain,
% 7.77/1.50      ( r2_relset_1(sK2,sK2,sK3,sK4) != iProver_top ),
% 7.77/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_9576,plain,
% 7.77/1.50      ( k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))
% 7.77/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.77/1.50      inference(global_propositional_subsumption,
% 7.77/1.50                [status(thm)],
% 7.77/1.50                [c_9423,c_27]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_12,plain,
% 7.77/1.50      ( r2_relset_1(X0,X1,X2,X3)
% 7.77/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.77/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.77/1.50      | m1_subset_1(sK1(X0,X1,X2,X3),X1) ),
% 7.77/1.50      inference(cnf_transformation,[],[f46]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_1081,plain,
% 7.77/1.50      ( r2_relset_1(X0,X1,X2,X3) = iProver_top
% 7.77/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.50      | m1_subset_1(sK1(X0,X1,X2,X3),X1) = iProver_top ),
% 7.77/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_2,plain,
% 7.77/1.50      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 7.77/1.50      inference(cnf_transformation,[],[f36]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_1091,plain,
% 7.77/1.50      ( m1_subset_1(X0,X1) != iProver_top
% 7.77/1.50      | v1_xboole_0(X1) != iProver_top
% 7.77/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.77/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_3406,plain,
% 7.77/1.50      ( r2_relset_1(X0,X1,X2,X3) = iProver_top
% 7.77/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.50      | v1_xboole_0(X1) != iProver_top
% 7.77/1.50      | v1_xboole_0(sK1(X0,X1,X2,X3)) = iProver_top ),
% 7.77/1.50      inference(superposition,[status(thm)],[c_1081,c_1091]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_7905,plain,
% 7.77/1.50      ( r2_relset_1(sK2,sK2,sK3,X0) = iProver_top
% 7.77/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 7.77/1.50      | v1_xboole_0(sK1(sK2,sK2,sK3,X0)) = iProver_top
% 7.77/1.50      | v1_xboole_0(sK2) != iProver_top ),
% 7.77/1.50      inference(superposition,[status(thm)],[c_1072,c_3406]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_8613,plain,
% 7.77/1.50      ( r2_relset_1(sK2,sK2,sK3,sK4) = iProver_top
% 7.77/1.50      | v1_xboole_0(sK1(sK2,sK2,sK3,sK4)) = iProver_top
% 7.77/1.50      | v1_xboole_0(sK2) != iProver_top ),
% 7.77/1.50      inference(superposition,[status(thm)],[c_1073,c_7905]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_8706,plain,
% 7.77/1.50      ( v1_xboole_0(sK1(sK2,sK2,sK3,sK4)) = iProver_top
% 7.77/1.50      | v1_xboole_0(sK2) != iProver_top ),
% 7.77/1.50      inference(global_propositional_subsumption,
% 7.77/1.50                [status(thm)],
% 7.77/1.50                [c_8613,c_27]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_0,plain,
% 7.77/1.50      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 7.77/1.50      inference(cnf_transformation,[],[f33]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_1093,plain,
% 7.77/1.50      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.77/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_8712,plain,
% 7.77/1.50      ( sK1(sK2,sK2,sK3,sK4) = k1_xboole_0
% 7.77/1.50      | v1_xboole_0(sK2) != iProver_top ),
% 7.77/1.50      inference(superposition,[status(thm)],[c_8706,c_1093]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_9583,plain,
% 7.77/1.50      ( sK1(sK2,sK2,sK3,sK4) = k1_xboole_0
% 7.77/1.50      | k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4)) ),
% 7.77/1.50      inference(superposition,[status(thm)],[c_9576,c_8712]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_669,plain,
% 7.77/1.50      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.77/1.50      | r2_relset_1(X4,X5,X6,X7)
% 7.77/1.50      | X4 != X0
% 7.77/1.50      | X5 != X1
% 7.77/1.50      | X6 != X2
% 7.77/1.50      | X7 != X3 ),
% 7.77/1.50      theory(equality) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_16,plain,
% 7.77/1.50      ( r2_relset_1(X0,X1,X2,X2)
% 7.77/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 7.77/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_1743,plain,
% 7.77/1.50      ( r2_relset_1(sK2,sK2,sK3,sK3) ),
% 7.77/1.50      inference(resolution,[status(thm)],[c_16,c_21]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_3736,plain,
% 7.77/1.50      ( r2_relset_1(X0,X1,X2,X3)
% 7.77/1.50      | X2 != sK3
% 7.77/1.50      | X3 != sK3
% 7.77/1.50      | X0 != sK2
% 7.77/1.50      | X1 != sK2 ),
% 7.77/1.50      inference(resolution,[status(thm)],[c_669,c_1743]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_4623,plain,
% 7.77/1.50      ( sK4 != sK3 | sK3 != sK3 | sK2 != sK2 ),
% 7.77/1.50      inference(resolution,[status(thm)],[c_3736,c_18]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_4624,plain,
% 7.77/1.50      ( sK4 != sK3 ),
% 7.77/1.50      inference(equality_resolution_simp,[status(thm)],[c_4623]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_9,plain,
% 7.77/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.50      | ~ v1_xboole_0(X1)
% 7.77/1.50      | v1_xboole_0(X0) ),
% 7.77/1.50      inference(cnf_transformation,[],[f42]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_1084,plain,
% 7.77/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.77/1.50      | v1_xboole_0(X1) != iProver_top
% 7.77/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.77/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_2435,plain,
% 7.77/1.50      ( v1_xboole_0(sK3) = iProver_top
% 7.77/1.50      | v1_xboole_0(sK2) != iProver_top ),
% 7.77/1.50      inference(superposition,[status(thm)],[c_1072,c_1084]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_9587,plain,
% 7.77/1.50      ( k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))
% 7.77/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.77/1.50      inference(superposition,[status(thm)],[c_9576,c_2435]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_10055,plain,
% 7.77/1.50      ( k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))
% 7.77/1.50      | sK3 = k1_xboole_0 ),
% 7.77/1.50      inference(superposition,[status(thm)],[c_9587,c_1093]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_2434,plain,
% 7.77/1.50      ( v1_xboole_0(sK4) = iProver_top
% 7.77/1.50      | v1_xboole_0(sK2) != iProver_top ),
% 7.77/1.50      inference(superposition,[status(thm)],[c_1073,c_1084]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_9588,plain,
% 7.77/1.50      ( k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))
% 7.77/1.50      | v1_xboole_0(sK4) = iProver_top ),
% 7.77/1.50      inference(superposition,[status(thm)],[c_9576,c_2434]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_10059,plain,
% 7.77/1.50      ( k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))
% 7.77/1.50      | sK4 = k1_xboole_0 ),
% 7.77/1.50      inference(superposition,[status(thm)],[c_9588,c_1093]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_661,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_1537,plain,
% 7.77/1.50      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 7.77/1.50      inference(instantiation,[status(thm)],[c_661]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_7317,plain,
% 7.77/1.50      ( X0 = sK3 | X0 != k1_xboole_0 | sK3 != k1_xboole_0 ),
% 7.77/1.50      inference(instantiation,[status(thm)],[c_1537]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_10804,plain,
% 7.77/1.50      ( sK4 = sK3 | sK4 != k1_xboole_0 | sK3 != k1_xboole_0 ),
% 7.77/1.50      inference(instantiation,[status(thm)],[c_7317]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_10861,plain,
% 7.77/1.50      ( k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) = k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4)) ),
% 7.77/1.50      inference(global_propositional_subsumption,
% 7.77/1.50                [status(thm)],
% 7.77/1.50                [c_9583,c_4624,c_10055,c_10059,c_10804]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_7,plain,
% 7.77/1.50      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 7.77/1.50      | r2_hidden(k4_tarski(X2,X0),X1)
% 7.77/1.50      | ~ v1_relat_1(X1) ),
% 7.77/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_1086,plain,
% 7.77/1.50      ( r2_hidden(X0,k11_relat_1(X1,X2)) != iProver_top
% 7.77/1.50      | r2_hidden(k4_tarski(X2,X0),X1) = iProver_top
% 7.77/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.77/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_10864,plain,
% 7.77/1.50      ( r2_hidden(X0,k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) != iProver_top
% 7.77/1.50      | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),X0),sK4) = iProver_top
% 7.77/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.77/1.50      inference(superposition,[status(thm)],[c_10861,c_1086]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_6,plain,
% 7.77/1.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.77/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_47,plain,
% 7.77/1.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.77/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_49,plain,
% 7.77/1.50      ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) = iProver_top ),
% 7.77/1.50      inference(instantiation,[status(thm)],[c_47]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_5,plain,
% 7.77/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.77/1.50      | ~ v1_relat_1(X1)
% 7.77/1.50      | v1_relat_1(X0) ),
% 7.77/1.50      inference(cnf_transformation,[],[f38]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_1504,plain,
% 7.77/1.50      ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK2)) | v1_relat_1(sK4) ),
% 7.77/1.50      inference(resolution,[status(thm)],[c_5,c_20]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_1505,plain,
% 7.77/1.50      ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) != iProver_top
% 7.77/1.50      | v1_relat_1(sK4) = iProver_top ),
% 7.77/1.50      inference(predicate_to_equality,[status(thm)],[c_1504]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_11276,plain,
% 7.77/1.50      ( r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),X0),sK4) = iProver_top
% 7.77/1.50      | r2_hidden(X0,k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) != iProver_top ),
% 7.77/1.50      inference(global_propositional_subsumption,
% 7.77/1.50                [status(thm)],
% 7.77/1.50                [c_10864,c_49,c_1505]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_11277,plain,
% 7.77/1.50      ( r2_hidden(X0,k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) != iProver_top
% 7.77/1.50      | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),X0),sK4) = iProver_top ),
% 7.77/1.50      inference(renaming,[status(thm)],[c_11276]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_24438,plain,
% 7.77/1.50      ( r2_relset_1(sK2,sK2,sK3,sK4) = iProver_top
% 7.77/1.50      | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4) = iProver_top
% 7.77/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 7.77/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 7.77/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.77/1.50      inference(superposition,[status(thm)],[c_3602,c_11277]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_663,plain,
% 7.77/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.77/1.50      theory(equality) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_2942,plain,
% 7.77/1.50      ( r2_hidden(X0,X1)
% 7.77/1.50      | ~ r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4)))
% 7.77/1.50      | X0 != sK1(sK2,sK2,sK3,sK4)
% 7.77/1.50      | X1 != k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4)) ),
% 7.77/1.50      inference(instantiation,[status(thm)],[c_663]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_8588,plain,
% 7.77/1.50      ( r2_hidden(sK1(sK2,sK2,sK3,sK4),X0)
% 7.77/1.50      | ~ r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4)))
% 7.77/1.50      | X0 != k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))
% 7.77/1.50      | sK1(sK2,sK2,sK3,sK4) != sK1(sK2,sK2,sK3,sK4) ),
% 7.77/1.50      inference(instantiation,[status(thm)],[c_2942]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_13437,plain,
% 7.77/1.50      ( ~ r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4)))
% 7.77/1.50      | r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)))
% 7.77/1.50      | sK1(sK2,sK2,sK3,sK4) != sK1(sK2,sK2,sK3,sK4)
% 7.77/1.50      | k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) != k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4)) ),
% 7.77/1.50      inference(instantiation,[status(thm)],[c_8588]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_13438,plain,
% 7.77/1.50      ( sK1(sK2,sK2,sK3,sK4) != sK1(sK2,sK2,sK3,sK4)
% 7.77/1.50      | k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)) != k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))
% 7.77/1.50      | r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))) != iProver_top
% 7.77/1.50      | r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) = iProver_top ),
% 7.77/1.50      inference(predicate_to_equality,[status(thm)],[c_13437]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_4640,plain,
% 7.77/1.50      ( ~ r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4)))
% 7.77/1.50      | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3)
% 7.77/1.50      | ~ v1_relat_1(sK3) ),
% 7.77/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_4641,plain,
% 7.77/1.50      ( r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK3,sK0(sK2,sK2,sK3,sK4))) != iProver_top
% 7.77/1.50      | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3) = iProver_top
% 7.77/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.77/1.50      inference(predicate_to_equality,[status(thm)],[c_4640]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_660,plain,( X0 = X0 ),theory(equality) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_2094,plain,
% 7.77/1.50      ( sK1(sK2,sK2,sK3,sK4) = sK1(sK2,sK2,sK3,sK4) ),
% 7.77/1.50      inference(instantiation,[status(thm)],[c_660]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_1872,plain,
% 7.77/1.50      ( r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4)))
% 7.77/1.50      | ~ r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4)
% 7.77/1.50      | ~ v1_relat_1(sK4) ),
% 7.77/1.50      inference(instantiation,[status(thm)],[c_8]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_1873,plain,
% 7.77/1.50      ( r2_hidden(sK1(sK2,sK2,sK3,sK4),k11_relat_1(sK4,sK0(sK2,sK2,sK3,sK4))) = iProver_top
% 7.77/1.50      | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4) != iProver_top
% 7.77/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.77/1.50      inference(predicate_to_equality,[status(thm)],[c_1872]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_1506,plain,
% 7.77/1.50      ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK2)) | v1_relat_1(sK3) ),
% 7.77/1.50      inference(resolution,[status(thm)],[c_5,c_21]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_1507,plain,
% 7.77/1.50      ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) != iProver_top
% 7.77/1.50      | v1_relat_1(sK3) = iProver_top ),
% 7.77/1.50      inference(predicate_to_equality,[status(thm)],[c_1506]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_10,plain,
% 7.77/1.50      ( r2_relset_1(X0,X1,X2,X3)
% 7.77/1.50      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3)
% 7.77/1.50      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2)
% 7.77/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.77/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 7.77/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_552,plain,
% 7.77/1.50      ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X3)
% 7.77/1.50      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2,X3),sK1(X0,X1,X2,X3)),X2)
% 7.77/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.77/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.77/1.50      | sK4 != X3
% 7.77/1.50      | sK3 != X2
% 7.77/1.50      | sK2 != X1
% 7.77/1.50      | sK2 != X0 ),
% 7.77/1.50      inference(resolution_lifted,[status(thm)],[c_10,c_18]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_553,plain,
% 7.77/1.50      ( ~ r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4)
% 7.77/1.50      | ~ r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3)
% 7.77/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 7.77/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 7.77/1.50      inference(unflattening,[status(thm)],[c_552]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_555,plain,
% 7.77/1.50      ( ~ r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4)
% 7.77/1.50      | ~ r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3) ),
% 7.77/1.50      inference(global_propositional_subsumption,
% 7.77/1.50                [status(thm)],
% 7.77/1.50                [c_553,c_21,c_20]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_557,plain,
% 7.77/1.50      ( r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK4) != iProver_top
% 7.77/1.50      | r2_hidden(k4_tarski(sK0(sK2,sK2,sK3,sK4),sK1(sK2,sK2,sK3,sK4)),sK3) != iProver_top ),
% 7.77/1.50      inference(predicate_to_equality,[status(thm)],[c_555]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_23,plain,
% 7.77/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 7.77/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(c_22,plain,
% 7.77/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 7.77/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.77/1.50  
% 7.77/1.50  cnf(contradiction,plain,
% 7.77/1.50      ( $false ),
% 7.77/1.50      inference(minisat,
% 7.77/1.50                [status(thm)],
% 7.77/1.50                [c_24438,c_13438,c_10861,c_4641,c_2094,c_1873,c_1507,
% 7.77/1.50                 c_1505,c_557,c_49,c_27,c_23,c_22]) ).
% 7.77/1.50  
% 7.77/1.50  
% 7.77/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.77/1.50  
% 7.77/1.50  ------                               Statistics
% 7.77/1.50  
% 7.77/1.50  ------ Selected
% 7.77/1.50  
% 7.77/1.50  total_time:                             0.796
% 7.77/1.50  
%------------------------------------------------------------------------------
