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
% DateTime   : Thu Dec  3 12:09:33 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 344 expanded)
%              Number of clauses        :   68 (  86 expanded)
%              Number of leaves         :   17 ( 118 expanded)
%              Depth                    :   16
%              Number of atoms          :  471 (1969 expanded)
%              Number of equality atoms :   77 (  85 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
                 => r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
                   => r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)))) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3))))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3))))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3))))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ r1_tarski(k5_setfam_1(X0,sK5),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,sK5))))
        & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3))))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ~ r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,sK4,k7_funct_2(X0,X1,sK4,X3))))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK4,X0,X1)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3))))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,sK3,X2,k7_funct_2(X0,sK3,X2,X3))))
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
            & v1_funct_2(X2,X0,sK3)
            & v1_funct_1(X2) )
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3))))
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_setfam_1(sK2,X3),k5_setfam_1(sK2,k6_funct_2(sK2,X1,X2,k7_funct_2(sK2,X1,X2,X3))))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK2))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
              & v1_funct_2(X2,sK2,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ~ r1_tarski(k5_setfam_1(sK2,sK5),k5_setfam_1(sK2,k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,sK5))))
    & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f23,f37,f36,f35,f34])).

fof(f62,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f30])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ~ r1_tarski(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
        | ~ r1_tarski(X0,k3_tarski(X1)) )
      & ( r1_tarski(X0,k3_tarski(X1))
        | ~ m1_setfam_1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f60,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f57,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f63,plain,(
    ~ r1_tarski(k5_setfam_1(sK2,sK5),k5_setfam_1(sK2,k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,sK5)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(X0))
                     => ( m1_setfam_1(X3,X4)
                       => m1_setfam_1(k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_setfam_1(k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)),X4)
                      | ~ m1_setfam_1(X3,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_setfam_1(k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)),X4)
                      | ~ m1_setfam_1(X3,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_setfam_1(k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)),X4)
      | ~ m1_setfam_1(X3,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
      | ~ r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1134,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1136,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1464,plain,
    ( r1_tarski(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1134,c_1136])).

cnf(c_8,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | r1_tarski(k3_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1141,plain,
    ( r2_hidden(sK1(X0,X1),X0) = iProver_top
    | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_196,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_197,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_196])).

cnf(c_248,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_197])).

cnf(c_1132,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_248])).

cnf(c_2315,plain,
    ( r2_hidden(sK1(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1141,c_1132])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1143,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4228,plain,
    ( r1_tarski(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(sK1(X0,X2),X1) = iProver_top
    | r1_tarski(k3_tarski(X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2315,c_1143])).

cnf(c_7,plain,
    ( ~ r1_tarski(sK1(X0,X1),X1)
    | r1_tarski(k3_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1142,plain,
    ( r1_tarski(sK1(X0,X1),X1) != iProver_top
    | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6952,plain,
    ( r1_tarski(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4228,c_1142])).

cnf(c_7220,plain,
    ( r1_tarski(k3_tarski(sK5),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1464,c_6952])).

cnf(c_11,plain,
    ( ~ m1_setfam_1(X0,X1)
    | r1_tarski(X1,k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1139,plain,
    ( m1_setfam_1(X0,X1) != iProver_top
    | r1_tarski(X1,k3_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k7_funct_2(X1,X2,X0,X3),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k7_funct_2(X1,X2,X0,X3),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_365,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | m1_subset_1(k7_funct_2(sK2,sK3,sK4,X0),k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_24,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_369,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | m1_subset_1(k7_funct_2(sK2,sK3,sK4,X0),k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_365,c_24,c_23,c_22,c_20])).

cnf(c_1130,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top
    | m1_subset_1(k7_funct_2(sK2,sK3,sK4,X0),k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_369])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | m1_subset_1(k6_funct_2(X1,X2,X0,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_382,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | m1_subset_1(k6_funct_2(X1,X2,X0,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0)
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_383,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | m1_subset_1(k6_funct_2(sK2,sK3,sK4,X0),k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_387,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | m1_subset_1(k6_funct_2(sK2,sK3,sK4,X0),k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_383,c_24,c_23,c_22,c_20])).

cnf(c_1129,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
    | m1_subset_1(k6_funct_2(sK2,sK3,sK4,X0),k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_387])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k5_setfam_1(X1,X0) = k3_tarski(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1138,plain,
    ( k5_setfam_1(X0,X1) = k3_tarski(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2174,plain,
    ( k5_setfam_1(sK2,k6_funct_2(sK2,sK3,sK4,X0)) = k3_tarski(k6_funct_2(sK2,sK3,sK4,X0))
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1129,c_1138])).

cnf(c_3129,plain,
    ( k5_setfam_1(sK2,k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,X0))) = k3_tarski(k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1130,c_2174])).

cnf(c_3634,plain,
    ( k5_setfam_1(sK2,k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,sK5))) = k3_tarski(k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,sK5))) ),
    inference(superposition,[status(thm)],[c_1134,c_3129])).

cnf(c_2172,plain,
    ( k5_setfam_1(sK2,sK5) = k3_tarski(sK5) ),
    inference(superposition,[status(thm)],[c_1134,c_1138])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(k5_setfam_1(sK2,sK5),k5_setfam_1(sK2,k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,sK5)))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1135,plain,
    ( r1_tarski(k5_setfam_1(sK2,sK5),k5_setfam_1(sK2,k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,sK5)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2690,plain,
    ( r1_tarski(k3_tarski(sK5),k5_setfam_1(sK2,k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,sK5)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2172,c_1135])).

cnf(c_3653,plain,
    ( r1_tarski(k3_tarski(sK5),k3_tarski(k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,sK5)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3634,c_2690])).

cnf(c_3766,plain,
    ( m1_setfam_1(k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,sK5)),k3_tarski(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1139,c_3653])).

cnf(c_1867,plain,
    ( m1_subset_1(k3_tarski(sK5),k1_zfmisc_1(sK2))
    | ~ r1_tarski(k3_tarski(sK5),sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1868,plain,
    ( m1_subset_1(k3_tarski(sK5),k1_zfmisc_1(sK2)) = iProver_top
    | r1_tarski(k3_tarski(sK5),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1867])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_setfam_1(X3,X4)
    | m1_setfam_1(k6_funct_2(X1,X2,X0,k7_funct_2(X1,X2,X0,X3)),X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_340,plain,
    ( ~ m1_setfam_1(X0,X1)
    | m1_setfam_1(k6_funct_2(X2,X3,X4,k7_funct_2(X2,X3,X4,X0)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4)
    | sK4 != X4
    | sK3 != X3
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_21])).

cnf(c_341,plain,
    ( ~ m1_setfam_1(X0,X1)
    | m1_setfam_1(k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_345,plain,
    ( ~ m1_setfam_1(X0,X1)
    | m1_setfam_1(k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_341,c_24,c_23,c_22,c_20])).

cnf(c_1280,plain,
    ( m1_setfam_1(k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,sK5)),X0)
    | ~ m1_setfam_1(sK5,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_345])).

cnf(c_1699,plain,
    ( m1_setfam_1(k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,sK5)),k3_tarski(sK5))
    | ~ m1_setfam_1(sK5,k3_tarski(sK5))
    | ~ m1_subset_1(k3_tarski(sK5),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_1280])).

cnf(c_1702,plain,
    ( m1_setfam_1(k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,sK5)),k3_tarski(sK5)) = iProver_top
    | m1_setfam_1(sK5,k3_tarski(sK5)) != iProver_top
    | m1_subset_1(k3_tarski(sK5),k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1699])).

cnf(c_10,plain,
    ( m1_setfam_1(X0,X1)
    | ~ r1_tarski(X1,k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1293,plain,
    ( m1_setfam_1(X0,k3_tarski(X0))
    | ~ r1_tarski(k3_tarski(X0),k3_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1698,plain,
    ( m1_setfam_1(sK5,k3_tarski(sK5))
    | ~ r1_tarski(k3_tarski(sK5),k3_tarski(sK5)) ),
    inference(instantiation,[status(thm)],[c_1293])).

cnf(c_1700,plain,
    ( m1_setfam_1(sK5,k3_tarski(sK5)) = iProver_top
    | r1_tarski(k3_tarski(sK5),k3_tarski(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1698])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1294,plain,
    ( r1_tarski(k3_tarski(X0),k3_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1659,plain,
    ( r1_tarski(k3_tarski(sK5),k3_tarski(sK5)) ),
    inference(instantiation,[status(thm)],[c_1294])).

cnf(c_1661,plain,
    ( r1_tarski(k3_tarski(sK5),k3_tarski(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1659])).

cnf(c_30,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7220,c_3766,c_1868,c_1702,c_1700,c_1661,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:01:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.77/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.01  
% 2.77/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.77/1.01  
% 2.77/1.01  ------  iProver source info
% 2.77/1.01  
% 2.77/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.77/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.77/1.01  git: non_committed_changes: false
% 2.77/1.01  git: last_make_outside_of_git: false
% 2.77/1.01  
% 2.77/1.01  ------ 
% 2.77/1.01  
% 2.77/1.01  ------ Input Options
% 2.77/1.01  
% 2.77/1.01  --out_options                           all
% 2.77/1.01  --tptp_safe_out                         true
% 2.77/1.01  --problem_path                          ""
% 2.77/1.01  --include_path                          ""
% 2.77/1.01  --clausifier                            res/vclausify_rel
% 2.77/1.01  --clausifier_options                    --mode clausify
% 2.77/1.01  --stdin                                 false
% 2.77/1.01  --stats_out                             all
% 2.77/1.01  
% 2.77/1.01  ------ General Options
% 2.77/1.01  
% 2.77/1.01  --fof                                   false
% 2.77/1.01  --time_out_real                         305.
% 2.77/1.01  --time_out_virtual                      -1.
% 2.77/1.01  --symbol_type_check                     false
% 2.77/1.01  --clausify_out                          false
% 2.77/1.01  --sig_cnt_out                           false
% 2.77/1.01  --trig_cnt_out                          false
% 2.77/1.01  --trig_cnt_out_tolerance                1.
% 2.77/1.01  --trig_cnt_out_sk_spl                   false
% 2.77/1.01  --abstr_cl_out                          false
% 2.77/1.01  
% 2.77/1.01  ------ Global Options
% 2.77/1.01  
% 2.77/1.01  --schedule                              default
% 2.77/1.01  --add_important_lit                     false
% 2.77/1.01  --prop_solver_per_cl                    1000
% 2.77/1.01  --min_unsat_core                        false
% 2.77/1.01  --soft_assumptions                      false
% 2.77/1.01  --soft_lemma_size                       3
% 2.77/1.01  --prop_impl_unit_size                   0
% 2.77/1.01  --prop_impl_unit                        []
% 2.77/1.01  --share_sel_clauses                     true
% 2.77/1.01  --reset_solvers                         false
% 2.77/1.01  --bc_imp_inh                            [conj_cone]
% 2.77/1.01  --conj_cone_tolerance                   3.
% 2.77/1.01  --extra_neg_conj                        none
% 2.77/1.01  --large_theory_mode                     true
% 2.77/1.01  --prolific_symb_bound                   200
% 2.77/1.01  --lt_threshold                          2000
% 2.77/1.01  --clause_weak_htbl                      true
% 2.77/1.01  --gc_record_bc_elim                     false
% 2.77/1.01  
% 2.77/1.01  ------ Preprocessing Options
% 2.77/1.01  
% 2.77/1.01  --preprocessing_flag                    true
% 2.77/1.01  --time_out_prep_mult                    0.1
% 2.77/1.01  --splitting_mode                        input
% 2.77/1.01  --splitting_grd                         true
% 2.77/1.01  --splitting_cvd                         false
% 2.77/1.01  --splitting_cvd_svl                     false
% 2.77/1.01  --splitting_nvd                         32
% 2.77/1.01  --sub_typing                            true
% 2.77/1.01  --prep_gs_sim                           true
% 2.77/1.01  --prep_unflatten                        true
% 2.77/1.01  --prep_res_sim                          true
% 2.77/1.01  --prep_upred                            true
% 2.77/1.01  --prep_sem_filter                       exhaustive
% 2.77/1.01  --prep_sem_filter_out                   false
% 2.77/1.01  --pred_elim                             true
% 2.77/1.01  --res_sim_input                         true
% 2.77/1.01  --eq_ax_congr_red                       true
% 2.77/1.01  --pure_diseq_elim                       true
% 2.77/1.01  --brand_transform                       false
% 2.77/1.01  --non_eq_to_eq                          false
% 2.77/1.01  --prep_def_merge                        true
% 2.77/1.01  --prep_def_merge_prop_impl              false
% 2.77/1.01  --prep_def_merge_mbd                    true
% 2.77/1.01  --prep_def_merge_tr_red                 false
% 2.77/1.01  --prep_def_merge_tr_cl                  false
% 2.77/1.01  --smt_preprocessing                     true
% 2.77/1.01  --smt_ac_axioms                         fast
% 2.77/1.01  --preprocessed_out                      false
% 2.77/1.01  --preprocessed_stats                    false
% 2.77/1.01  
% 2.77/1.01  ------ Abstraction refinement Options
% 2.77/1.01  
% 2.77/1.01  --abstr_ref                             []
% 2.77/1.01  --abstr_ref_prep                        false
% 2.77/1.01  --abstr_ref_until_sat                   false
% 2.77/1.01  --abstr_ref_sig_restrict                funpre
% 2.77/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.77/1.01  --abstr_ref_under                       []
% 2.77/1.01  
% 2.77/1.01  ------ SAT Options
% 2.77/1.01  
% 2.77/1.01  --sat_mode                              false
% 2.77/1.01  --sat_fm_restart_options                ""
% 2.77/1.01  --sat_gr_def                            false
% 2.77/1.01  --sat_epr_types                         true
% 2.77/1.01  --sat_non_cyclic_types                  false
% 2.77/1.01  --sat_finite_models                     false
% 2.77/1.01  --sat_fm_lemmas                         false
% 2.77/1.01  --sat_fm_prep                           false
% 2.77/1.01  --sat_fm_uc_incr                        true
% 2.77/1.01  --sat_out_model                         small
% 2.77/1.01  --sat_out_clauses                       false
% 2.77/1.01  
% 2.77/1.01  ------ QBF Options
% 2.77/1.01  
% 2.77/1.01  --qbf_mode                              false
% 2.77/1.01  --qbf_elim_univ                         false
% 2.77/1.01  --qbf_dom_inst                          none
% 2.77/1.01  --qbf_dom_pre_inst                      false
% 2.77/1.01  --qbf_sk_in                             false
% 2.77/1.01  --qbf_pred_elim                         true
% 2.77/1.01  --qbf_split                             512
% 2.77/1.01  
% 2.77/1.01  ------ BMC1 Options
% 2.77/1.01  
% 2.77/1.01  --bmc1_incremental                      false
% 2.77/1.01  --bmc1_axioms                           reachable_all
% 2.77/1.01  --bmc1_min_bound                        0
% 2.77/1.01  --bmc1_max_bound                        -1
% 2.77/1.01  --bmc1_max_bound_default                -1
% 2.77/1.01  --bmc1_symbol_reachability              true
% 2.77/1.01  --bmc1_property_lemmas                  false
% 2.77/1.01  --bmc1_k_induction                      false
% 2.77/1.01  --bmc1_non_equiv_states                 false
% 2.77/1.01  --bmc1_deadlock                         false
% 2.77/1.01  --bmc1_ucm                              false
% 2.77/1.01  --bmc1_add_unsat_core                   none
% 2.77/1.01  --bmc1_unsat_core_children              false
% 2.77/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.77/1.01  --bmc1_out_stat                         full
% 2.77/1.01  --bmc1_ground_init                      false
% 2.77/1.01  --bmc1_pre_inst_next_state              false
% 2.77/1.01  --bmc1_pre_inst_state                   false
% 2.77/1.01  --bmc1_pre_inst_reach_state             false
% 2.77/1.01  --bmc1_out_unsat_core                   false
% 2.77/1.01  --bmc1_aig_witness_out                  false
% 2.77/1.01  --bmc1_verbose                          false
% 2.77/1.01  --bmc1_dump_clauses_tptp                false
% 2.77/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.77/1.01  --bmc1_dump_file                        -
% 2.77/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.77/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.77/1.01  --bmc1_ucm_extend_mode                  1
% 2.77/1.01  --bmc1_ucm_init_mode                    2
% 2.77/1.01  --bmc1_ucm_cone_mode                    none
% 2.77/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.77/1.01  --bmc1_ucm_relax_model                  4
% 2.77/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.77/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.77/1.01  --bmc1_ucm_layered_model                none
% 2.77/1.01  --bmc1_ucm_max_lemma_size               10
% 2.77/1.01  
% 2.77/1.01  ------ AIG Options
% 2.77/1.01  
% 2.77/1.01  --aig_mode                              false
% 2.77/1.01  
% 2.77/1.01  ------ Instantiation Options
% 2.77/1.01  
% 2.77/1.01  --instantiation_flag                    true
% 2.77/1.01  --inst_sos_flag                         false
% 2.77/1.01  --inst_sos_phase                        true
% 2.77/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.77/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.77/1.01  --inst_lit_sel_side                     num_symb
% 2.77/1.01  --inst_solver_per_active                1400
% 2.77/1.01  --inst_solver_calls_frac                1.
% 2.77/1.01  --inst_passive_queue_type               priority_queues
% 2.77/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.77/1.01  --inst_passive_queues_freq              [25;2]
% 2.77/1.01  --inst_dismatching                      true
% 2.77/1.01  --inst_eager_unprocessed_to_passive     true
% 2.77/1.01  --inst_prop_sim_given                   true
% 2.77/1.01  --inst_prop_sim_new                     false
% 2.77/1.01  --inst_subs_new                         false
% 2.77/1.01  --inst_eq_res_simp                      false
% 2.77/1.01  --inst_subs_given                       false
% 2.77/1.01  --inst_orphan_elimination               true
% 2.77/1.01  --inst_learning_loop_flag               true
% 2.77/1.01  --inst_learning_start                   3000
% 2.77/1.01  --inst_learning_factor                  2
% 2.77/1.01  --inst_start_prop_sim_after_learn       3
% 2.77/1.01  --inst_sel_renew                        solver
% 2.77/1.01  --inst_lit_activity_flag                true
% 2.77/1.01  --inst_restr_to_given                   false
% 2.77/1.01  --inst_activity_threshold               500
% 2.77/1.01  --inst_out_proof                        true
% 2.77/1.01  
% 2.77/1.01  ------ Resolution Options
% 2.77/1.01  
% 2.77/1.01  --resolution_flag                       true
% 2.77/1.01  --res_lit_sel                           adaptive
% 2.77/1.01  --res_lit_sel_side                      none
% 2.77/1.01  --res_ordering                          kbo
% 2.77/1.01  --res_to_prop_solver                    active
% 2.77/1.01  --res_prop_simpl_new                    false
% 2.77/1.01  --res_prop_simpl_given                  true
% 2.77/1.01  --res_passive_queue_type                priority_queues
% 2.77/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.77/1.01  --res_passive_queues_freq               [15;5]
% 2.77/1.01  --res_forward_subs                      full
% 2.77/1.01  --res_backward_subs                     full
% 2.77/1.01  --res_forward_subs_resolution           true
% 2.77/1.01  --res_backward_subs_resolution          true
% 2.77/1.01  --res_orphan_elimination                true
% 2.77/1.01  --res_time_limit                        2.
% 2.77/1.01  --res_out_proof                         true
% 2.77/1.01  
% 2.77/1.01  ------ Superposition Options
% 2.77/1.01  
% 2.77/1.01  --superposition_flag                    true
% 2.77/1.01  --sup_passive_queue_type                priority_queues
% 2.77/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.77/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.77/1.01  --demod_completeness_check              fast
% 2.77/1.01  --demod_use_ground                      true
% 2.77/1.01  --sup_to_prop_solver                    passive
% 2.77/1.01  --sup_prop_simpl_new                    true
% 2.77/1.01  --sup_prop_simpl_given                  true
% 2.77/1.01  --sup_fun_splitting                     false
% 2.77/1.01  --sup_smt_interval                      50000
% 2.77/1.01  
% 2.77/1.01  ------ Superposition Simplification Setup
% 2.77/1.01  
% 2.77/1.01  --sup_indices_passive                   []
% 2.77/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.77/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.01  --sup_full_bw                           [BwDemod]
% 2.77/1.01  --sup_immed_triv                        [TrivRules]
% 2.77/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.77/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.01  --sup_immed_bw_main                     []
% 2.77/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.77/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.01  
% 2.77/1.01  ------ Combination Options
% 2.77/1.01  
% 2.77/1.01  --comb_res_mult                         3
% 2.77/1.01  --comb_sup_mult                         2
% 2.77/1.01  --comb_inst_mult                        10
% 2.77/1.01  
% 2.77/1.01  ------ Debug Options
% 2.77/1.01  
% 2.77/1.01  --dbg_backtrace                         false
% 2.77/1.01  --dbg_dump_prop_clauses                 false
% 2.77/1.01  --dbg_dump_prop_clauses_file            -
% 2.77/1.01  --dbg_out_stat                          false
% 2.77/1.01  ------ Parsing...
% 2.77/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.77/1.01  
% 2.77/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.77/1.01  
% 2.77/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.77/1.01  
% 2.77/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.77/1.01  ------ Proving...
% 2.77/1.01  ------ Problem Properties 
% 2.77/1.01  
% 2.77/1.01  
% 2.77/1.01  clauses                                 20
% 2.77/1.01  conjectures                             3
% 2.77/1.01  EPR                                     3
% 2.77/1.01  Horn                                    18
% 2.77/1.01  unary                                   4
% 2.77/1.01  binary                                  11
% 2.77/1.01  lits                                    42
% 2.77/1.01  lits eq                                 4
% 2.77/1.01  fd_pure                                 0
% 2.77/1.01  fd_pseudo                               0
% 2.77/1.01  fd_cond                                 0
% 2.77/1.01  fd_pseudo_cond                          3
% 2.77/1.01  AC symbols                              0
% 2.77/1.01  
% 2.77/1.01  ------ Schedule dynamic 5 is on 
% 2.77/1.01  
% 2.77/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.77/1.01  
% 2.77/1.01  
% 2.77/1.01  ------ 
% 2.77/1.01  Current options:
% 2.77/1.01  ------ 
% 2.77/1.01  
% 2.77/1.01  ------ Input Options
% 2.77/1.01  
% 2.77/1.01  --out_options                           all
% 2.77/1.01  --tptp_safe_out                         true
% 2.77/1.01  --problem_path                          ""
% 2.77/1.01  --include_path                          ""
% 2.77/1.01  --clausifier                            res/vclausify_rel
% 2.77/1.01  --clausifier_options                    --mode clausify
% 2.77/1.01  --stdin                                 false
% 2.77/1.01  --stats_out                             all
% 2.77/1.01  
% 2.77/1.01  ------ General Options
% 2.77/1.01  
% 2.77/1.01  --fof                                   false
% 2.77/1.01  --time_out_real                         305.
% 2.77/1.01  --time_out_virtual                      -1.
% 2.77/1.01  --symbol_type_check                     false
% 2.77/1.01  --clausify_out                          false
% 2.77/1.01  --sig_cnt_out                           false
% 2.77/1.01  --trig_cnt_out                          false
% 2.77/1.01  --trig_cnt_out_tolerance                1.
% 2.77/1.01  --trig_cnt_out_sk_spl                   false
% 2.77/1.01  --abstr_cl_out                          false
% 2.77/1.01  
% 2.77/1.01  ------ Global Options
% 2.77/1.01  
% 2.77/1.01  --schedule                              default
% 2.77/1.01  --add_important_lit                     false
% 2.77/1.01  --prop_solver_per_cl                    1000
% 2.77/1.01  --min_unsat_core                        false
% 2.77/1.01  --soft_assumptions                      false
% 2.77/1.01  --soft_lemma_size                       3
% 2.77/1.01  --prop_impl_unit_size                   0
% 2.77/1.01  --prop_impl_unit                        []
% 2.77/1.01  --share_sel_clauses                     true
% 2.77/1.01  --reset_solvers                         false
% 2.77/1.01  --bc_imp_inh                            [conj_cone]
% 2.77/1.01  --conj_cone_tolerance                   3.
% 2.77/1.01  --extra_neg_conj                        none
% 2.77/1.01  --large_theory_mode                     true
% 2.77/1.01  --prolific_symb_bound                   200
% 2.77/1.01  --lt_threshold                          2000
% 2.77/1.01  --clause_weak_htbl                      true
% 2.77/1.01  --gc_record_bc_elim                     false
% 2.77/1.01  
% 2.77/1.01  ------ Preprocessing Options
% 2.77/1.01  
% 2.77/1.01  --preprocessing_flag                    true
% 2.77/1.01  --time_out_prep_mult                    0.1
% 2.77/1.01  --splitting_mode                        input
% 2.77/1.01  --splitting_grd                         true
% 2.77/1.01  --splitting_cvd                         false
% 2.77/1.01  --splitting_cvd_svl                     false
% 2.77/1.01  --splitting_nvd                         32
% 2.77/1.01  --sub_typing                            true
% 2.77/1.01  --prep_gs_sim                           true
% 2.77/1.01  --prep_unflatten                        true
% 2.77/1.01  --prep_res_sim                          true
% 2.77/1.01  --prep_upred                            true
% 2.77/1.01  --prep_sem_filter                       exhaustive
% 2.77/1.01  --prep_sem_filter_out                   false
% 2.77/1.01  --pred_elim                             true
% 2.77/1.01  --res_sim_input                         true
% 2.77/1.01  --eq_ax_congr_red                       true
% 2.77/1.01  --pure_diseq_elim                       true
% 2.77/1.01  --brand_transform                       false
% 2.77/1.01  --non_eq_to_eq                          false
% 2.77/1.01  --prep_def_merge                        true
% 2.77/1.01  --prep_def_merge_prop_impl              false
% 2.77/1.01  --prep_def_merge_mbd                    true
% 2.77/1.01  --prep_def_merge_tr_red                 false
% 2.77/1.01  --prep_def_merge_tr_cl                  false
% 2.77/1.01  --smt_preprocessing                     true
% 2.77/1.01  --smt_ac_axioms                         fast
% 2.77/1.01  --preprocessed_out                      false
% 2.77/1.01  --preprocessed_stats                    false
% 2.77/1.01  
% 2.77/1.01  ------ Abstraction refinement Options
% 2.77/1.01  
% 2.77/1.01  --abstr_ref                             []
% 2.77/1.01  --abstr_ref_prep                        false
% 2.77/1.01  --abstr_ref_until_sat                   false
% 2.77/1.01  --abstr_ref_sig_restrict                funpre
% 2.77/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.77/1.01  --abstr_ref_under                       []
% 2.77/1.01  
% 2.77/1.01  ------ SAT Options
% 2.77/1.01  
% 2.77/1.01  --sat_mode                              false
% 2.77/1.01  --sat_fm_restart_options                ""
% 2.77/1.02  --sat_gr_def                            false
% 2.77/1.02  --sat_epr_types                         true
% 2.77/1.02  --sat_non_cyclic_types                  false
% 2.77/1.02  --sat_finite_models                     false
% 2.77/1.02  --sat_fm_lemmas                         false
% 2.77/1.02  --sat_fm_prep                           false
% 2.77/1.02  --sat_fm_uc_incr                        true
% 2.77/1.02  --sat_out_model                         small
% 2.77/1.02  --sat_out_clauses                       false
% 2.77/1.02  
% 2.77/1.02  ------ QBF Options
% 2.77/1.02  
% 2.77/1.02  --qbf_mode                              false
% 2.77/1.02  --qbf_elim_univ                         false
% 2.77/1.02  --qbf_dom_inst                          none
% 2.77/1.02  --qbf_dom_pre_inst                      false
% 2.77/1.02  --qbf_sk_in                             false
% 2.77/1.02  --qbf_pred_elim                         true
% 2.77/1.02  --qbf_split                             512
% 2.77/1.02  
% 2.77/1.02  ------ BMC1 Options
% 2.77/1.02  
% 2.77/1.02  --bmc1_incremental                      false
% 2.77/1.02  --bmc1_axioms                           reachable_all
% 2.77/1.02  --bmc1_min_bound                        0
% 2.77/1.02  --bmc1_max_bound                        -1
% 2.77/1.02  --bmc1_max_bound_default                -1
% 2.77/1.02  --bmc1_symbol_reachability              true
% 2.77/1.02  --bmc1_property_lemmas                  false
% 2.77/1.02  --bmc1_k_induction                      false
% 2.77/1.02  --bmc1_non_equiv_states                 false
% 2.77/1.02  --bmc1_deadlock                         false
% 2.77/1.02  --bmc1_ucm                              false
% 2.77/1.02  --bmc1_add_unsat_core                   none
% 2.77/1.02  --bmc1_unsat_core_children              false
% 2.77/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.77/1.02  --bmc1_out_stat                         full
% 2.77/1.02  --bmc1_ground_init                      false
% 2.77/1.02  --bmc1_pre_inst_next_state              false
% 2.77/1.02  --bmc1_pre_inst_state                   false
% 2.77/1.02  --bmc1_pre_inst_reach_state             false
% 2.77/1.02  --bmc1_out_unsat_core                   false
% 2.77/1.02  --bmc1_aig_witness_out                  false
% 2.77/1.02  --bmc1_verbose                          false
% 2.77/1.02  --bmc1_dump_clauses_tptp                false
% 2.77/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.77/1.02  --bmc1_dump_file                        -
% 2.77/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.77/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.77/1.02  --bmc1_ucm_extend_mode                  1
% 2.77/1.02  --bmc1_ucm_init_mode                    2
% 2.77/1.02  --bmc1_ucm_cone_mode                    none
% 2.77/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.77/1.02  --bmc1_ucm_relax_model                  4
% 2.77/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.77/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.77/1.02  --bmc1_ucm_layered_model                none
% 2.77/1.02  --bmc1_ucm_max_lemma_size               10
% 2.77/1.02  
% 2.77/1.02  ------ AIG Options
% 2.77/1.02  
% 2.77/1.02  --aig_mode                              false
% 2.77/1.02  
% 2.77/1.02  ------ Instantiation Options
% 2.77/1.02  
% 2.77/1.02  --instantiation_flag                    true
% 2.77/1.02  --inst_sos_flag                         false
% 2.77/1.02  --inst_sos_phase                        true
% 2.77/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.77/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.77/1.02  --inst_lit_sel_side                     none
% 2.77/1.02  --inst_solver_per_active                1400
% 2.77/1.02  --inst_solver_calls_frac                1.
% 2.77/1.02  --inst_passive_queue_type               priority_queues
% 2.77/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.77/1.02  --inst_passive_queues_freq              [25;2]
% 2.77/1.02  --inst_dismatching                      true
% 2.77/1.02  --inst_eager_unprocessed_to_passive     true
% 2.77/1.02  --inst_prop_sim_given                   true
% 2.77/1.02  --inst_prop_sim_new                     false
% 2.77/1.02  --inst_subs_new                         false
% 2.77/1.02  --inst_eq_res_simp                      false
% 2.77/1.02  --inst_subs_given                       false
% 2.77/1.02  --inst_orphan_elimination               true
% 2.77/1.02  --inst_learning_loop_flag               true
% 2.77/1.02  --inst_learning_start                   3000
% 2.77/1.02  --inst_learning_factor                  2
% 2.77/1.02  --inst_start_prop_sim_after_learn       3
% 2.77/1.02  --inst_sel_renew                        solver
% 2.77/1.02  --inst_lit_activity_flag                true
% 2.77/1.02  --inst_restr_to_given                   false
% 2.77/1.02  --inst_activity_threshold               500
% 2.77/1.02  --inst_out_proof                        true
% 2.77/1.02  
% 2.77/1.02  ------ Resolution Options
% 2.77/1.02  
% 2.77/1.02  --resolution_flag                       false
% 2.77/1.02  --res_lit_sel                           adaptive
% 2.77/1.02  --res_lit_sel_side                      none
% 2.77/1.02  --res_ordering                          kbo
% 2.77/1.02  --res_to_prop_solver                    active
% 2.77/1.02  --res_prop_simpl_new                    false
% 2.77/1.02  --res_prop_simpl_given                  true
% 2.77/1.02  --res_passive_queue_type                priority_queues
% 2.77/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.77/1.02  --res_passive_queues_freq               [15;5]
% 2.77/1.02  --res_forward_subs                      full
% 2.77/1.02  --res_backward_subs                     full
% 2.77/1.02  --res_forward_subs_resolution           true
% 2.77/1.02  --res_backward_subs_resolution          true
% 2.77/1.02  --res_orphan_elimination                true
% 2.77/1.02  --res_time_limit                        2.
% 2.77/1.02  --res_out_proof                         true
% 2.77/1.02  
% 2.77/1.02  ------ Superposition Options
% 2.77/1.02  
% 2.77/1.02  --superposition_flag                    true
% 2.77/1.02  --sup_passive_queue_type                priority_queues
% 2.77/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.77/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.77/1.02  --demod_completeness_check              fast
% 2.77/1.02  --demod_use_ground                      true
% 2.77/1.02  --sup_to_prop_solver                    passive
% 2.77/1.02  --sup_prop_simpl_new                    true
% 2.77/1.02  --sup_prop_simpl_given                  true
% 2.77/1.02  --sup_fun_splitting                     false
% 2.77/1.02  --sup_smt_interval                      50000
% 2.77/1.02  
% 2.77/1.02  ------ Superposition Simplification Setup
% 2.77/1.02  
% 2.77/1.02  --sup_indices_passive                   []
% 2.77/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.77/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.02  --sup_full_bw                           [BwDemod]
% 2.77/1.02  --sup_immed_triv                        [TrivRules]
% 2.77/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.77/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.02  --sup_immed_bw_main                     []
% 2.77/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.77/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.02  
% 2.77/1.02  ------ Combination Options
% 2.77/1.02  
% 2.77/1.02  --comb_res_mult                         3
% 2.77/1.02  --comb_sup_mult                         2
% 2.77/1.02  --comb_inst_mult                        10
% 2.77/1.02  
% 2.77/1.02  ------ Debug Options
% 2.77/1.02  
% 2.77/1.02  --dbg_backtrace                         false
% 2.77/1.02  --dbg_dump_prop_clauses                 false
% 2.77/1.02  --dbg_dump_prop_clauses_file            -
% 2.77/1.02  --dbg_out_stat                          false
% 2.77/1.02  
% 2.77/1.02  
% 2.77/1.02  
% 2.77/1.02  
% 2.77/1.02  ------ Proving...
% 2.77/1.02  
% 2.77/1.02  
% 2.77/1.02  % SZS status Theorem for theBenchmark.p
% 2.77/1.02  
% 2.77/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.77/1.02  
% 2.77/1.02  fof(f11,conjecture,(
% 2.77/1.02    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) => r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3))))))))),
% 2.77/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f12,negated_conjecture,(
% 2.77/1.02    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) => r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3))))))))),
% 2.77/1.02    inference(negated_conjecture,[],[f11])).
% 2.77/1.02  
% 2.77/1.02  fof(f22,plain,(
% 2.77/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.77/1.02    inference(ennf_transformation,[],[f12])).
% 2.77/1.02  
% 2.77/1.02  fof(f23,plain,(
% 2.77/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.77/1.02    inference(flattening,[],[f22])).
% 2.77/1.02  
% 2.77/1.02  fof(f37,plain,(
% 2.77/1.02    ( ! [X2,X0,X1] : (? [X3] : (~r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (~r1_tarski(k5_setfam_1(X0,sK5),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,sK5)))) & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(X0))))) )),
% 2.77/1.02    introduced(choice_axiom,[])).
% 2.77/1.02  
% 2.77/1.02  fof(f36,plain,(
% 2.77/1.02    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,sK4,k7_funct_2(X0,X1,sK4,X3)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK4,X0,X1) & v1_funct_1(sK4))) )),
% 2.77/1.02    introduced(choice_axiom,[])).
% 2.77/1.02  
% 2.77/1.02  fof(f35,plain,(
% 2.77/1.02    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,sK3,X2,k7_funct_2(X0,sK3,X2,X3)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) & v1_funct_2(X2,X0,sK3) & v1_funct_1(X2)) & ~v1_xboole_0(sK3))) )),
% 2.77/1.02    introduced(choice_axiom,[])).
% 2.77/1.02  
% 2.77/1.02  fof(f34,plain,(
% 2.77/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_setfam_1(X0,X3),k5_setfam_1(X0,k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_setfam_1(sK2,X3),k5_setfam_1(sK2,k6_funct_2(sK2,X1,X2,k7_funct_2(sK2,X1,X2,X3)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X2,sK2,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK2))),
% 2.77/1.02    introduced(choice_axiom,[])).
% 2.77/1.02  
% 2.77/1.02  fof(f38,plain,(
% 2.77/1.02    (((~r1_tarski(k5_setfam_1(sK2,sK5),k5_setfam_1(sK2,k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,sK5)))) & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK2)))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 2.77/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f23,f37,f36,f35,f34])).
% 2.77/1.02  
% 2.77/1.02  fof(f62,plain,(
% 2.77/1.02    m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 2.77/1.02    inference(cnf_transformation,[],[f38])).
% 2.77/1.02  
% 2.77/1.02  fof(f7,axiom,(
% 2.77/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.77/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f33,plain,(
% 2.77/1.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.77/1.02    inference(nnf_transformation,[],[f7])).
% 2.77/1.02  
% 2.77/1.02  fof(f52,plain,(
% 2.77/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.77/1.02    inference(cnf_transformation,[],[f33])).
% 2.77/1.02  
% 2.77/1.02  fof(f3,axiom,(
% 2.77/1.02    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 2.77/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f13,plain,(
% 2.77/1.02    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 2.77/1.02    inference(ennf_transformation,[],[f3])).
% 2.77/1.02  
% 2.77/1.02  fof(f30,plain,(
% 2.77/1.02    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.77/1.02    introduced(choice_axiom,[])).
% 2.77/1.02  
% 2.77/1.02  fof(f31,plain,(
% 2.77/1.02    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.77/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f30])).
% 2.77/1.02  
% 2.77/1.02  fof(f46,plain,(
% 2.77/1.02    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 2.77/1.02    inference(cnf_transformation,[],[f31])).
% 2.77/1.02  
% 2.77/1.02  fof(f4,axiom,(
% 2.77/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.77/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f14,plain,(
% 2.77/1.02    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.77/1.02    inference(ennf_transformation,[],[f4])).
% 2.77/1.02  
% 2.77/1.02  fof(f48,plain,(
% 2.77/1.02    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.77/1.02    inference(cnf_transformation,[],[f14])).
% 2.77/1.02  
% 2.77/1.02  fof(f53,plain,(
% 2.77/1.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.77/1.02    inference(cnf_transformation,[],[f33])).
% 2.77/1.02  
% 2.77/1.02  fof(f2,axiom,(
% 2.77/1.02    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.77/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f26,plain,(
% 2.77/1.02    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.77/1.02    inference(nnf_transformation,[],[f2])).
% 2.77/1.02  
% 2.77/1.02  fof(f27,plain,(
% 2.77/1.02    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.77/1.02    inference(rectify,[],[f26])).
% 2.77/1.02  
% 2.77/1.02  fof(f28,plain,(
% 2.77/1.02    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 2.77/1.02    introduced(choice_axiom,[])).
% 2.77/1.02  
% 2.77/1.02  fof(f29,plain,(
% 2.77/1.02    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.77/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 2.77/1.02  
% 2.77/1.02  fof(f42,plain,(
% 2.77/1.02    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.77/1.02    inference(cnf_transformation,[],[f29])).
% 2.77/1.02  
% 2.77/1.02  fof(f67,plain,(
% 2.77/1.02    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 2.77/1.02    inference(equality_resolution,[],[f42])).
% 2.77/1.02  
% 2.77/1.02  fof(f47,plain,(
% 2.77/1.02    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ~r1_tarski(sK1(X0,X1),X1)) )),
% 2.77/1.02    inference(cnf_transformation,[],[f31])).
% 2.77/1.02  
% 2.77/1.02  fof(f5,axiom,(
% 2.77/1.02    ! [X0,X1] : (m1_setfam_1(X1,X0) <=> r1_tarski(X0,k3_tarski(X1)))),
% 2.77/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f32,plain,(
% 2.77/1.02    ! [X0,X1] : ((m1_setfam_1(X1,X0) | ~r1_tarski(X0,k3_tarski(X1))) & (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)))),
% 2.77/1.02    inference(nnf_transformation,[],[f5])).
% 2.77/1.02  
% 2.77/1.02  fof(f49,plain,(
% 2.77/1.02    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)) )),
% 2.77/1.02    inference(cnf_transformation,[],[f32])).
% 2.77/1.02  
% 2.77/1.02  fof(f9,axiom,(
% 2.77/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1))))),
% 2.77/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f18,plain,(
% 2.77/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.77/1.02    inference(ennf_transformation,[],[f9])).
% 2.77/1.02  
% 2.77/1.02  fof(f19,plain,(
% 2.77/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.77/1.02    inference(flattening,[],[f18])).
% 2.77/1.02  
% 2.77/1.02  fof(f55,plain,(
% 2.77/1.02    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.77/1.02    inference(cnf_transformation,[],[f19])).
% 2.77/1.02  
% 2.77/1.02  fof(f60,plain,(
% 2.77/1.02    v1_funct_2(sK4,sK2,sK3)),
% 2.77/1.02    inference(cnf_transformation,[],[f38])).
% 2.77/1.02  
% 2.77/1.02  fof(f57,plain,(
% 2.77/1.02    ~v1_xboole_0(sK2)),
% 2.77/1.02    inference(cnf_transformation,[],[f38])).
% 2.77/1.02  
% 2.77/1.02  fof(f58,plain,(
% 2.77/1.02    ~v1_xboole_0(sK3)),
% 2.77/1.02    inference(cnf_transformation,[],[f38])).
% 2.77/1.02  
% 2.77/1.02  fof(f59,plain,(
% 2.77/1.02    v1_funct_1(sK4)),
% 2.77/1.02    inference(cnf_transformation,[],[f38])).
% 2.77/1.02  
% 2.77/1.02  fof(f61,plain,(
% 2.77/1.02    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.77/1.02    inference(cnf_transformation,[],[f38])).
% 2.77/1.02  
% 2.77/1.02  fof(f8,axiom,(
% 2.77/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.77/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f16,plain,(
% 2.77/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.77/1.02    inference(ennf_transformation,[],[f8])).
% 2.77/1.02  
% 2.77/1.02  fof(f17,plain,(
% 2.77/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.77/1.02    inference(flattening,[],[f16])).
% 2.77/1.02  
% 2.77/1.02  fof(f54,plain,(
% 2.77/1.02    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.77/1.02    inference(cnf_transformation,[],[f17])).
% 2.77/1.02  
% 2.77/1.02  fof(f6,axiom,(
% 2.77/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 2.77/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f15,plain,(
% 2.77/1.02    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.77/1.02    inference(ennf_transformation,[],[f6])).
% 2.77/1.02  
% 2.77/1.02  fof(f51,plain,(
% 2.77/1.02    ( ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.77/1.02    inference(cnf_transformation,[],[f15])).
% 2.77/1.02  
% 2.77/1.02  fof(f63,plain,(
% 2.77/1.02    ~r1_tarski(k5_setfam_1(sK2,sK5),k5_setfam_1(sK2,k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,sK5))))),
% 2.77/1.02    inference(cnf_transformation,[],[f38])).
% 2.77/1.02  
% 2.77/1.02  fof(f10,axiom,(
% 2.77/1.02    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => (m1_setfam_1(X3,X4) => m1_setfam_1(k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)),X4)))))))),
% 2.77/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f20,plain,(
% 2.77/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((m1_setfam_1(k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)),X4) | ~m1_setfam_1(X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.77/1.02    inference(ennf_transformation,[],[f10])).
% 2.77/1.02  
% 2.77/1.02  fof(f21,plain,(
% 2.77/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (m1_setfam_1(k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)),X4) | ~m1_setfam_1(X3,X4) | ~m1_subset_1(X4,k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.77/1.02    inference(flattening,[],[f20])).
% 2.77/1.02  
% 2.77/1.02  fof(f56,plain,(
% 2.77/1.02    ( ! [X4,X2,X0,X3,X1] : (m1_setfam_1(k6_funct_2(X0,X1,X2,k7_funct_2(X0,X1,X2,X3)),X4) | ~m1_setfam_1(X3,X4) | ~m1_subset_1(X4,k1_zfmisc_1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.77/1.02    inference(cnf_transformation,[],[f21])).
% 2.77/1.02  
% 2.77/1.02  fof(f50,plain,(
% 2.77/1.02    ( ! [X0,X1] : (m1_setfam_1(X1,X0) | ~r1_tarski(X0,k3_tarski(X1))) )),
% 2.77/1.02    inference(cnf_transformation,[],[f32])).
% 2.77/1.02  
% 2.77/1.02  fof(f1,axiom,(
% 2.77/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.77/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f24,plain,(
% 2.77/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.77/1.02    inference(nnf_transformation,[],[f1])).
% 2.77/1.02  
% 2.77/1.02  fof(f25,plain,(
% 2.77/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.77/1.02    inference(flattening,[],[f24])).
% 2.77/1.02  
% 2.77/1.02  fof(f39,plain,(
% 2.77/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.77/1.02    inference(cnf_transformation,[],[f25])).
% 2.77/1.02  
% 2.77/1.02  fof(f65,plain,(
% 2.77/1.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.77/1.02    inference(equality_resolution,[],[f39])).
% 2.77/1.02  
% 2.77/1.02  cnf(c_19,negated_conjecture,
% 2.77/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 2.77/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1134,plain,
% 2.77/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_14,plain,
% 2.77/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.77/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1136,plain,
% 2.77/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.77/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1464,plain,
% 2.77/1.02      ( r1_tarski(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 2.77/1.02      inference(superposition,[status(thm)],[c_1134,c_1136]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_8,plain,
% 2.77/1.02      ( r2_hidden(sK1(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1) ),
% 2.77/1.02      inference(cnf_transformation,[],[f46]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1141,plain,
% 2.77/1.02      ( r2_hidden(sK1(X0,X1),X0) = iProver_top
% 2.77/1.02      | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_9,plain,
% 2.77/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.77/1.02      | ~ r2_hidden(X2,X0)
% 2.77/1.02      | r2_hidden(X2,X1) ),
% 2.77/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_13,plain,
% 2.77/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.77/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_196,plain,
% 2.77/1.02      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.77/1.02      inference(prop_impl,[status(thm)],[c_13]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_197,plain,
% 2.77/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.77/1.02      inference(renaming,[status(thm)],[c_196]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_248,plain,
% 2.77/1.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.77/1.02      inference(bin_hyper_res,[status(thm)],[c_9,c_197]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1132,plain,
% 2.77/1.02      ( r2_hidden(X0,X1) != iProver_top
% 2.77/1.02      | r2_hidden(X0,X2) = iProver_top
% 2.77/1.02      | r1_tarski(X1,X2) != iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_248]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2315,plain,
% 2.77/1.02      ( r2_hidden(sK1(X0,X1),X2) = iProver_top
% 2.77/1.02      | r1_tarski(X0,X2) != iProver_top
% 2.77/1.02      | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
% 2.77/1.02      inference(superposition,[status(thm)],[c_1141,c_1132]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_6,plain,
% 2.77/1.02      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.77/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1143,plain,
% 2.77/1.02      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.77/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_4228,plain,
% 2.77/1.02      ( r1_tarski(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.77/1.02      | r1_tarski(sK1(X0,X2),X1) = iProver_top
% 2.77/1.02      | r1_tarski(k3_tarski(X0),X2) = iProver_top ),
% 2.77/1.02      inference(superposition,[status(thm)],[c_2315,c_1143]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_7,plain,
% 2.77/1.02      ( ~ r1_tarski(sK1(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1) ),
% 2.77/1.02      inference(cnf_transformation,[],[f47]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1142,plain,
% 2.77/1.02      ( r1_tarski(sK1(X0,X1),X1) != iProver_top
% 2.77/1.02      | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_6952,plain,
% 2.77/1.02      ( r1_tarski(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.77/1.02      | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
% 2.77/1.02      inference(superposition,[status(thm)],[c_4228,c_1142]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_7220,plain,
% 2.77/1.02      ( r1_tarski(k3_tarski(sK5),sK2) = iProver_top ),
% 2.77/1.02      inference(superposition,[status(thm)],[c_1464,c_6952]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_11,plain,
% 2.77/1.02      ( ~ m1_setfam_1(X0,X1) | r1_tarski(X1,k3_tarski(X0)) ),
% 2.77/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1139,plain,
% 2.77/1.02      ( m1_setfam_1(X0,X1) != iProver_top
% 2.77/1.02      | r1_tarski(X1,k3_tarski(X0)) = iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_16,plain,
% 2.77/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.77/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.77/1.02      | m1_subset_1(k7_funct_2(X1,X2,X0,X3),k1_zfmisc_1(k1_zfmisc_1(X2)))
% 2.77/1.02      | v1_xboole_0(X1)
% 2.77/1.02      | v1_xboole_0(X2)
% 2.77/1.02      | ~ v1_funct_1(X0) ),
% 2.77/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_21,negated_conjecture,
% 2.77/1.02      ( v1_funct_2(sK4,sK2,sK3) ),
% 2.77/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_364,plain,
% 2.77/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.77/1.02      | m1_subset_1(k7_funct_2(X1,X2,X0,X3),k1_zfmisc_1(k1_zfmisc_1(X2)))
% 2.77/1.02      | v1_xboole_0(X1)
% 2.77/1.02      | v1_xboole_0(X2)
% 2.77/1.02      | ~ v1_funct_1(X0)
% 2.77/1.02      | sK4 != X0
% 2.77/1.02      | sK3 != X2
% 2.77/1.02      | sK2 != X1 ),
% 2.77/1.02      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_365,plain,
% 2.77/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK2)))
% 2.77/1.02      | m1_subset_1(k7_funct_2(sK2,sK3,sK4,X0),k1_zfmisc_1(k1_zfmisc_1(sK3)))
% 2.77/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.77/1.02      | v1_xboole_0(sK3)
% 2.77/1.02      | v1_xboole_0(sK2)
% 2.77/1.02      | ~ v1_funct_1(sK4) ),
% 2.77/1.02      inference(unflattening,[status(thm)],[c_364]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_24,negated_conjecture,
% 2.77/1.02      ( ~ v1_xboole_0(sK2) ),
% 2.77/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_23,negated_conjecture,
% 2.77/1.02      ( ~ v1_xboole_0(sK3) ),
% 2.77/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_22,negated_conjecture,
% 2.77/1.02      ( v1_funct_1(sK4) ),
% 2.77/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_20,negated_conjecture,
% 2.77/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.77/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_369,plain,
% 2.77/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK2)))
% 2.77/1.02      | m1_subset_1(k7_funct_2(sK2,sK3,sK4,X0),k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
% 2.77/1.02      inference(global_propositional_subsumption,
% 2.77/1.02                [status(thm)],
% 2.77/1.02                [c_365,c_24,c_23,c_22,c_20]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1130,plain,
% 2.77/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top
% 2.77/1.02      | m1_subset_1(k7_funct_2(sK2,sK3,sK4,X0),k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_369]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_15,plain,
% 2.77/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.77/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
% 2.77/1.02      | m1_subset_1(k6_funct_2(X1,X2,X0,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.77/1.02      | v1_xboole_0(X1)
% 2.77/1.02      | v1_xboole_0(X2)
% 2.77/1.02      | ~ v1_funct_1(X0) ),
% 2.77/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_382,plain,
% 2.77/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
% 2.77/1.02      | m1_subset_1(k6_funct_2(X1,X2,X0,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.77/1.02      | v1_xboole_0(X1)
% 2.77/1.02      | v1_xboole_0(X2)
% 2.77/1.02      | ~ v1_funct_1(X0)
% 2.77/1.02      | sK4 != X0
% 2.77/1.02      | sK3 != X2
% 2.77/1.02      | sK2 != X1 ),
% 2.77/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_21]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_383,plain,
% 2.77/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK3)))
% 2.77/1.02      | m1_subset_1(k6_funct_2(sK2,sK3,sK4,X0),k1_zfmisc_1(k1_zfmisc_1(sK2)))
% 2.77/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.77/1.02      | v1_xboole_0(sK3)
% 2.77/1.02      | v1_xboole_0(sK2)
% 2.77/1.02      | ~ v1_funct_1(sK4) ),
% 2.77/1.02      inference(unflattening,[status(thm)],[c_382]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_387,plain,
% 2.77/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK3)))
% 2.77/1.02      | m1_subset_1(k6_funct_2(sK2,sK3,sK4,X0),k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 2.77/1.02      inference(global_propositional_subsumption,
% 2.77/1.02                [status(thm)],
% 2.77/1.02                [c_383,c_24,c_23,c_22,c_20]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1129,plain,
% 2.77/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
% 2.77/1.02      | m1_subset_1(k6_funct_2(sK2,sK3,sK4,X0),k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_387]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_12,plain,
% 2.77/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.77/1.02      | k5_setfam_1(X1,X0) = k3_tarski(X0) ),
% 2.77/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1138,plain,
% 2.77/1.02      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
% 2.77/1.02      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2174,plain,
% 2.77/1.02      ( k5_setfam_1(sK2,k6_funct_2(sK2,sK3,sK4,X0)) = k3_tarski(k6_funct_2(sK2,sK3,sK4,X0))
% 2.77/1.02      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top ),
% 2.77/1.02      inference(superposition,[status(thm)],[c_1129,c_1138]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_3129,plain,
% 2.77/1.02      ( k5_setfam_1(sK2,k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,X0))) = k3_tarski(k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,X0)))
% 2.77/1.02      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top ),
% 2.77/1.02      inference(superposition,[status(thm)],[c_1130,c_2174]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_3634,plain,
% 2.77/1.02      ( k5_setfam_1(sK2,k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,sK5))) = k3_tarski(k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,sK5))) ),
% 2.77/1.02      inference(superposition,[status(thm)],[c_1134,c_3129]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2172,plain,
% 2.77/1.02      ( k5_setfam_1(sK2,sK5) = k3_tarski(sK5) ),
% 2.77/1.02      inference(superposition,[status(thm)],[c_1134,c_1138]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_18,negated_conjecture,
% 2.77/1.02      ( ~ r1_tarski(k5_setfam_1(sK2,sK5),k5_setfam_1(sK2,k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,sK5)))) ),
% 2.77/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1135,plain,
% 2.77/1.02      ( r1_tarski(k5_setfam_1(sK2,sK5),k5_setfam_1(sK2,k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,sK5)))) != iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2690,plain,
% 2.77/1.02      ( r1_tarski(k3_tarski(sK5),k5_setfam_1(sK2,k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,sK5)))) != iProver_top ),
% 2.77/1.02      inference(demodulation,[status(thm)],[c_2172,c_1135]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_3653,plain,
% 2.77/1.02      ( r1_tarski(k3_tarski(sK5),k3_tarski(k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,sK5)))) != iProver_top ),
% 2.77/1.02      inference(demodulation,[status(thm)],[c_3634,c_2690]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_3766,plain,
% 2.77/1.02      ( m1_setfam_1(k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,sK5)),k3_tarski(sK5)) != iProver_top ),
% 2.77/1.02      inference(superposition,[status(thm)],[c_1139,c_3653]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1867,plain,
% 2.77/1.02      ( m1_subset_1(k3_tarski(sK5),k1_zfmisc_1(sK2))
% 2.77/1.02      | ~ r1_tarski(k3_tarski(sK5),sK2) ),
% 2.77/1.02      inference(instantiation,[status(thm)],[c_13]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1868,plain,
% 2.77/1.02      ( m1_subset_1(k3_tarski(sK5),k1_zfmisc_1(sK2)) = iProver_top
% 2.77/1.02      | r1_tarski(k3_tarski(sK5),sK2) != iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_1867]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_17,plain,
% 2.77/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.77/1.02      | ~ m1_setfam_1(X3,X4)
% 2.77/1.02      | m1_setfam_1(k6_funct_2(X1,X2,X0,k7_funct_2(X1,X2,X0,X3)),X4)
% 2.77/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
% 2.77/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.77/1.02      | v1_xboole_0(X1)
% 2.77/1.02      | v1_xboole_0(X2)
% 2.77/1.02      | ~ v1_funct_1(X0) ),
% 2.77/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_340,plain,
% 2.77/1.02      ( ~ m1_setfam_1(X0,X1)
% 2.77/1.02      | m1_setfam_1(k6_funct_2(X2,X3,X4,k7_funct_2(X2,X3,X4,X0)),X1)
% 2.77/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 2.77/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.77/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X2)))
% 2.77/1.02      | v1_xboole_0(X2)
% 2.77/1.02      | v1_xboole_0(X3)
% 2.77/1.02      | ~ v1_funct_1(X4)
% 2.77/1.02      | sK4 != X4
% 2.77/1.02      | sK3 != X3
% 2.77/1.02      | sK2 != X2 ),
% 2.77/1.02      inference(resolution_lifted,[status(thm)],[c_17,c_21]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_341,plain,
% 2.77/1.02      ( ~ m1_setfam_1(X0,X1)
% 2.77/1.02      | m1_setfam_1(k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,X0)),X1)
% 2.77/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK2)))
% 2.77/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(sK2))
% 2.77/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.77/1.02      | v1_xboole_0(sK3)
% 2.77/1.02      | v1_xboole_0(sK2)
% 2.77/1.02      | ~ v1_funct_1(sK4) ),
% 2.77/1.02      inference(unflattening,[status(thm)],[c_340]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_345,plain,
% 2.77/1.02      ( ~ m1_setfam_1(X0,X1)
% 2.77/1.02      | m1_setfam_1(k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,X0)),X1)
% 2.77/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK2)))
% 2.77/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(sK2)) ),
% 2.77/1.02      inference(global_propositional_subsumption,
% 2.77/1.02                [status(thm)],
% 2.77/1.02                [c_341,c_24,c_23,c_22,c_20]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1280,plain,
% 2.77/1.02      ( m1_setfam_1(k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,sK5)),X0)
% 2.77/1.02      | ~ m1_setfam_1(sK5,X0)
% 2.77/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
% 2.77/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 2.77/1.02      inference(instantiation,[status(thm)],[c_345]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1699,plain,
% 2.77/1.02      ( m1_setfam_1(k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,sK5)),k3_tarski(sK5))
% 2.77/1.02      | ~ m1_setfam_1(sK5,k3_tarski(sK5))
% 2.77/1.02      | ~ m1_subset_1(k3_tarski(sK5),k1_zfmisc_1(sK2))
% 2.77/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 2.77/1.02      inference(instantiation,[status(thm)],[c_1280]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1702,plain,
% 2.77/1.02      ( m1_setfam_1(k6_funct_2(sK2,sK3,sK4,k7_funct_2(sK2,sK3,sK4,sK5)),k3_tarski(sK5)) = iProver_top
% 2.77/1.02      | m1_setfam_1(sK5,k3_tarski(sK5)) != iProver_top
% 2.77/1.02      | m1_subset_1(k3_tarski(sK5),k1_zfmisc_1(sK2)) != iProver_top
% 2.77/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_1699]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_10,plain,
% 2.77/1.02      ( m1_setfam_1(X0,X1) | ~ r1_tarski(X1,k3_tarski(X0)) ),
% 2.77/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1293,plain,
% 2.77/1.02      ( m1_setfam_1(X0,k3_tarski(X0))
% 2.77/1.02      | ~ r1_tarski(k3_tarski(X0),k3_tarski(X0)) ),
% 2.77/1.02      inference(instantiation,[status(thm)],[c_10]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1698,plain,
% 2.77/1.02      ( m1_setfam_1(sK5,k3_tarski(sK5))
% 2.77/1.02      | ~ r1_tarski(k3_tarski(sK5),k3_tarski(sK5)) ),
% 2.77/1.02      inference(instantiation,[status(thm)],[c_1293]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1700,plain,
% 2.77/1.02      ( m1_setfam_1(sK5,k3_tarski(sK5)) = iProver_top
% 2.77/1.02      | r1_tarski(k3_tarski(sK5),k3_tarski(sK5)) != iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_1698]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2,plain,
% 2.77/1.02      ( r1_tarski(X0,X0) ),
% 2.77/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1294,plain,
% 2.77/1.02      ( r1_tarski(k3_tarski(X0),k3_tarski(X0)) ),
% 2.77/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1659,plain,
% 2.77/1.02      ( r1_tarski(k3_tarski(sK5),k3_tarski(sK5)) ),
% 2.77/1.02      inference(instantiation,[status(thm)],[c_1294]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1661,plain,
% 2.77/1.02      ( r1_tarski(k3_tarski(sK5),k3_tarski(sK5)) = iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_1659]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_30,plain,
% 2.77/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(contradiction,plain,
% 2.77/1.02      ( $false ),
% 2.77/1.02      inference(minisat,
% 2.77/1.02                [status(thm)],
% 2.77/1.02                [c_7220,c_3766,c_1868,c_1702,c_1700,c_1661,c_30]) ).
% 2.77/1.02  
% 2.77/1.02  
% 2.77/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.77/1.02  
% 2.77/1.02  ------                               Statistics
% 2.77/1.02  
% 2.77/1.02  ------ General
% 2.77/1.02  
% 2.77/1.02  abstr_ref_over_cycles:                  0
% 2.77/1.02  abstr_ref_under_cycles:                 0
% 2.77/1.02  gc_basic_clause_elim:                   0
% 2.77/1.02  forced_gc_time:                         0
% 2.77/1.02  parsing_time:                           0.012
% 2.77/1.02  unif_index_cands_time:                  0.
% 2.77/1.02  unif_index_add_time:                    0.
% 2.77/1.02  orderings_time:                         0.
% 2.77/1.02  out_proof_time:                         0.01
% 2.77/1.02  total_time:                             0.279
% 2.77/1.02  num_of_symbols:                         50
% 2.77/1.02  num_of_terms:                           7048
% 2.77/1.02  
% 2.77/1.02  ------ Preprocessing
% 2.77/1.02  
% 2.77/1.02  num_of_splits:                          0
% 2.77/1.02  num_of_split_atoms:                     0
% 2.77/1.02  num_of_reused_defs:                     0
% 2.77/1.02  num_eq_ax_congr_red:                    18
% 2.77/1.02  num_of_sem_filtered_clauses:            1
% 2.77/1.02  num_of_subtypes:                        0
% 2.77/1.02  monotx_restored_types:                  0
% 2.77/1.02  sat_num_of_epr_types:                   0
% 2.77/1.02  sat_num_of_non_cyclic_types:            0
% 2.77/1.02  sat_guarded_non_collapsed_types:        0
% 2.77/1.02  num_pure_diseq_elim:                    0
% 2.77/1.02  simp_replaced_by:                       0
% 2.77/1.02  res_preprocessed:                       107
% 2.77/1.02  prep_upred:                             0
% 2.77/1.02  prep_unflattend:                        9
% 2.77/1.02  smt_new_axioms:                         0
% 2.77/1.02  pred_elim_cands:                        4
% 2.77/1.02  pred_elim:                              3
% 2.77/1.02  pred_elim_cl:                           4
% 2.77/1.02  pred_elim_cycles:                       5
% 2.77/1.02  merged_defs:                            24
% 2.77/1.02  merged_defs_ncl:                        0
% 2.77/1.02  bin_hyper_res:                          25
% 2.77/1.02  prep_cycles:                            4
% 2.77/1.02  pred_elim_time:                         0.004
% 2.77/1.02  splitting_time:                         0.
% 2.77/1.02  sem_filter_time:                        0.
% 2.77/1.02  monotx_time:                            0.001
% 2.77/1.02  subtype_inf_time:                       0.
% 2.77/1.02  
% 2.77/1.02  ------ Problem properties
% 2.77/1.02  
% 2.77/1.02  clauses:                                20
% 2.77/1.02  conjectures:                            3
% 2.77/1.02  epr:                                    3
% 2.77/1.02  horn:                                   18
% 2.77/1.02  ground:                                 3
% 2.77/1.02  unary:                                  4
% 2.77/1.02  binary:                                 11
% 2.77/1.02  lits:                                   42
% 2.77/1.02  lits_eq:                                4
% 2.77/1.02  fd_pure:                                0
% 2.77/1.02  fd_pseudo:                              0
% 2.77/1.02  fd_cond:                                0
% 2.77/1.02  fd_pseudo_cond:                         3
% 2.77/1.02  ac_symbols:                             0
% 2.77/1.02  
% 2.77/1.02  ------ Propositional Solver
% 2.77/1.02  
% 2.77/1.02  prop_solver_calls:                      27
% 2.77/1.02  prop_fast_solver_calls:                 728
% 2.77/1.02  smt_solver_calls:                       0
% 2.77/1.02  smt_fast_solver_calls:                  0
% 2.77/1.02  prop_num_of_clauses:                    2630
% 2.77/1.02  prop_preprocess_simplified:             7500
% 2.77/1.02  prop_fo_subsumed:                       14
% 2.77/1.02  prop_solver_time:                       0.
% 2.77/1.02  smt_solver_time:                        0.
% 2.77/1.02  smt_fast_solver_time:                   0.
% 2.77/1.02  prop_fast_solver_time:                  0.
% 2.77/1.02  prop_unsat_core_time:                   0.
% 2.77/1.02  
% 2.77/1.02  ------ QBF
% 2.77/1.02  
% 2.77/1.02  qbf_q_res:                              0
% 2.77/1.02  qbf_num_tautologies:                    0
% 2.77/1.02  qbf_prep_cycles:                        0
% 2.77/1.02  
% 2.77/1.02  ------ BMC1
% 2.77/1.02  
% 2.77/1.02  bmc1_current_bound:                     -1
% 2.77/1.02  bmc1_last_solved_bound:                 -1
% 2.77/1.02  bmc1_unsat_core_size:                   -1
% 2.77/1.02  bmc1_unsat_core_parents_size:           -1
% 2.77/1.02  bmc1_merge_next_fun:                    0
% 2.77/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.77/1.02  
% 2.77/1.02  ------ Instantiation
% 2.77/1.02  
% 2.77/1.02  inst_num_of_clauses:                    781
% 2.77/1.02  inst_num_in_passive:                    135
% 2.77/1.02  inst_num_in_active:                     428
% 2.77/1.02  inst_num_in_unprocessed:                218
% 2.77/1.02  inst_num_of_loops:                      450
% 2.77/1.02  inst_num_of_learning_restarts:          0
% 2.77/1.02  inst_num_moves_active_passive:          21
% 2.77/1.02  inst_lit_activity:                      0
% 2.77/1.02  inst_lit_activity_moves:                0
% 2.77/1.02  inst_num_tautologies:                   0
% 2.77/1.02  inst_num_prop_implied:                  0
% 2.77/1.02  inst_num_existing_simplified:           0
% 2.77/1.02  inst_num_eq_res_simplified:             0
% 2.77/1.02  inst_num_child_elim:                    0
% 2.77/1.02  inst_num_of_dismatching_blockings:      518
% 2.77/1.02  inst_num_of_non_proper_insts:           1003
% 2.77/1.02  inst_num_of_duplicates:                 0
% 2.77/1.02  inst_inst_num_from_inst_to_res:         0
% 2.77/1.02  inst_dismatching_checking_time:         0.
% 2.77/1.02  
% 2.77/1.02  ------ Resolution
% 2.77/1.02  
% 2.77/1.02  res_num_of_clauses:                     0
% 2.77/1.02  res_num_in_passive:                     0
% 2.77/1.02  res_num_in_active:                      0
% 2.77/1.02  res_num_of_loops:                       111
% 2.77/1.02  res_forward_subset_subsumed:            118
% 2.77/1.02  res_backward_subset_subsumed:           0
% 2.77/1.02  res_forward_subsumed:                   0
% 2.77/1.02  res_backward_subsumed:                  0
% 2.77/1.02  res_forward_subsumption_resolution:     0
% 2.77/1.02  res_backward_subsumption_resolution:    0
% 2.77/1.02  res_clause_to_clause_subsumption:       603
% 2.77/1.02  res_orphan_elimination:                 0
% 2.77/1.02  res_tautology_del:                      126
% 2.77/1.02  res_num_eq_res_simplified:              0
% 2.77/1.02  res_num_sel_changes:                    0
% 2.77/1.02  res_moves_from_active_to_pass:          0
% 2.77/1.02  
% 2.77/1.02  ------ Superposition
% 2.77/1.02  
% 2.77/1.02  sup_time_total:                         0.
% 2.77/1.02  sup_time_generating:                    0.
% 2.77/1.02  sup_time_sim_full:                      0.
% 2.77/1.02  sup_time_sim_immed:                     0.
% 2.77/1.02  
% 2.77/1.02  sup_num_of_clauses:                     137
% 2.77/1.02  sup_num_in_active:                      87
% 2.77/1.02  sup_num_in_passive:                     50
% 2.77/1.02  sup_num_of_loops:                       88
% 2.77/1.02  sup_fw_superposition:                   114
% 2.77/1.02  sup_bw_superposition:                   26
% 2.77/1.02  sup_immediate_simplified:               2
% 2.77/1.02  sup_given_eliminated:                   0
% 2.77/1.02  comparisons_done:                       0
% 2.77/1.02  comparisons_avoided:                    0
% 2.77/1.02  
% 2.77/1.02  ------ Simplifications
% 2.77/1.02  
% 2.77/1.02  
% 2.77/1.02  sim_fw_subset_subsumed:                 0
% 2.77/1.02  sim_bw_subset_subsumed:                 0
% 2.77/1.02  sim_fw_subsumed:                        2
% 2.77/1.02  sim_bw_subsumed:                        0
% 2.77/1.02  sim_fw_subsumption_res:                 0
% 2.77/1.02  sim_bw_subsumption_res:                 0
% 2.77/1.02  sim_tautology_del:                      3
% 2.77/1.02  sim_eq_tautology_del:                   4
% 2.77/1.02  sim_eq_res_simp:                        0
% 2.77/1.02  sim_fw_demodulated:                     0
% 2.77/1.02  sim_bw_demodulated:                     2
% 2.77/1.02  sim_light_normalised:                   0
% 2.77/1.02  sim_joinable_taut:                      0
% 2.77/1.02  sim_joinable_simp:                      0
% 2.77/1.02  sim_ac_normalised:                      0
% 2.77/1.02  sim_smt_subsumption:                    0
% 2.77/1.02  
%------------------------------------------------------------------------------
