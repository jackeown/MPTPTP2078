%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:27 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 699 expanded)
%              Number of clauses        :   70 ( 272 expanded)
%              Number of leaves         :   19 ( 167 expanded)
%              Depth                    :   12
%              Number of atoms          :  453 (2116 expanded)
%              Number of equality atoms :  228 ( 587 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ~ ( ! [X5,X6,X7,X8] :
            ~ ( k4_mcart_1(X5,X6,X7,X8) = X0
              & r2_hidden(X8,X4)
              & r2_hidden(X7,X3)
              & r2_hidden(X6,X2)
              & r2_hidden(X5,X1) )
        & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ~ ( ! [X5,X6,X7,X8] :
              ~ ( k4_mcart_1(X5,X6,X7,X8) = X0
                & r2_hidden(X8,X4)
                & r2_hidden(X7,X3)
                & r2_hidden(X6,X2)
                & r2_hidden(X5,X1) )
          & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f28,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ! [X5,X6,X7,X8] :
          ( k4_mcart_1(X5,X6,X7,X8) != X0
          | ~ r2_hidden(X8,X4)
          | ~ r2_hidden(X7,X3)
          | ~ r2_hidden(X6,X2)
          | ~ r2_hidden(X5,X1) )
      & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ! [X5,X6,X7,X8] :
            ( k4_mcart_1(X5,X6,X7,X8) != X0
            | ~ r2_hidden(X8,X4)
            | ~ r2_hidden(X7,X3)
            | ~ r2_hidden(X6,X2)
            | ~ r2_hidden(X5,X1) )
        & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) )
   => ( ! [X8,X7,X6,X5] :
          ( k4_mcart_1(X5,X6,X7,X8) != sK5
          | ~ r2_hidden(X8,sK9)
          | ~ r2_hidden(X7,sK8)
          | ~ r2_hidden(X6,sK7)
          | ~ r2_hidden(X5,sK6) )
      & r2_hidden(sK5,k4_zfmisc_1(sK6,sK7,sK8,sK9)) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ! [X5,X6,X7,X8] :
        ( k4_mcart_1(X5,X6,X7,X8) != sK5
        | ~ r2_hidden(X8,sK9)
        | ~ r2_hidden(X7,sK8)
        | ~ r2_hidden(X6,sK7)
        | ~ r2_hidden(X5,sK6) )
    & r2_hidden(sK5,k4_zfmisc_1(sK6,sK7,sK8,sK9)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f28,f39])).

fof(f63,plain,(
    r2_hidden(sK5,k4_zfmisc_1(sK6,sK7,sK8,sK9)) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f71,plain,(
    r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9)) ),
    inference(definition_unfolding,[],[f63,f62])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ? [X4] :
            ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ! [X6] :
                    ( m1_subset_1(X6,X1)
                   => ! [X7] :
                        ( m1_subset_1(X7,X2)
                       => ! [X8] :
                            ( m1_subset_1(X8,X3)
                           => k4_mcart_1(X5,X6,X7,X8) != X4 ) ) ) )
            & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ? [X8] :
                          ( k4_mcart_1(X5,X6,X7,X8) = X4
                          & m1_subset_1(X8,X3) )
                      & m1_subset_1(X7,X2) )
                  & m1_subset_1(X6,X1) )
              & m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X6,X7,X5,X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( k4_mcart_1(X5,X6,X7,X8) = X4
          & m1_subset_1(X8,X3) )
     => ( k4_mcart_1(X5,X6,X7,sK4(X0,X1,X2,X3,X4)) = X4
        & m1_subset_1(sK4(X0,X1,X2,X3,X4),X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ? [X8] :
              ( k4_mcart_1(X5,X6,X7,X8) = X4
              & m1_subset_1(X8,X3) )
          & m1_subset_1(X7,X2) )
     => ( ? [X8] :
            ( k4_mcart_1(X5,X6,sK3(X0,X1,X2,X3,X4),X8) = X4
            & m1_subset_1(X8,X3) )
        & m1_subset_1(sK3(X0,X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( k4_mcart_1(X5,X6,X7,X8) = X4
                  & m1_subset_1(X8,X3) )
              & m1_subset_1(X7,X2) )
          & m1_subset_1(X6,X1) )
     => ( ? [X7] :
            ( ? [X8] :
                ( k4_mcart_1(X5,sK2(X0,X1,X2,X3,X4),X7,X8) = X4
                & m1_subset_1(X8,X3) )
            & m1_subset_1(X7,X2) )
        & m1_subset_1(sK2(X0,X1,X2,X3,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( k4_mcart_1(X5,X6,X7,X8) = X4
                      & m1_subset_1(X8,X3) )
                  & m1_subset_1(X7,X2) )
              & m1_subset_1(X6,X1) )
          & m1_subset_1(X5,X0) )
     => ( ? [X6] :
            ( ? [X7] :
                ( ? [X8] :
                    ( k4_mcart_1(sK1(X0,X1,X2,X3,X4),X6,X7,X8) = X4
                    & m1_subset_1(X8,X3) )
                & m1_subset_1(X7,X2) )
            & m1_subset_1(X6,X1) )
        & m1_subset_1(sK1(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k4_mcart_1(sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4),sK3(X0,X1,X2,X3,X4),sK4(X0,X1,X2,X3,X4)) = X4
            & m1_subset_1(sK4(X0,X1,X2,X3,X4),X3)
            & m1_subset_1(sK3(X0,X1,X2,X3,X4),X2)
            & m1_subset_1(sK2(X0,X1,X2,X3,X4),X1)
            & m1_subset_1(sK1(X0,X1,X2,X3,X4),X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f27,f37,f36,f35,f34])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_mcart_1(sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4),sK3(X0,X1,X2,X3,X4),sK4(X0,X1,X2,X3,X4)) = X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k4_tarski(sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4)),sK3(X0,X1,X2,X3,X4)),sK4(X0,X1,X2,X3,X4)) = X4
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f60,f61,f62])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f43,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
    ! [X6,X8,X7,X5] :
      ( k4_mcart_1(X5,X6,X7,X8) != sK5
      | ~ r2_hidden(X8,sK9)
      | ~ r2_hidden(X7,sK8)
      | ~ r2_hidden(X6,sK7)
      | ~ r2_hidden(X5,sK6) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,(
    ! [X6,X8,X7,X5] :
      ( k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != sK5
      | ~ r2_hidden(X8,sK9)
      | ~ r2_hidden(X7,sK8)
      | ~ r2_hidden(X6,sK7)
      | ~ r2_hidden(X5,sK6) ) ),
    inference(definition_unfolding,[],[f64,f61])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK4(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK4(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f59,f62])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK3(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK3(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f58,f62])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK2(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK2(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f57,f62])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f56,f62])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1166,plain,
    ( r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_13,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1174,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1412,plain,
    ( m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_1174])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k4_tarski(k4_tarski(k4_tarski(sK1(X1,X2,X3,X4,X0),sK2(X1,X2,X3,X4,X0)),sK3(X1,X2,X3,X4,X0)),sK4(X1,X2,X3,X4,X0)) = X0
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1172,plain,
    ( k4_tarski(k4_tarski(k4_tarski(sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4)),sK3(X0,X1,X2,X3,X4)),sK4(X0,X1,X2,X3,X4)) = X4
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4574,plain,
    ( k4_tarski(k4_tarski(k4_tarski(sK1(sK6,sK7,sK8,sK9,sK5),sK2(sK6,sK7,sK8,sK9,sK5)),sK3(sK6,sK7,sK8,sK9,sK5)),sK4(sK6,sK7,sK8,sK9,sK5)) = sK5
    | sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | sK8 = k1_xboole_0
    | sK9 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1412,c_1172])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_55,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_58,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_71,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_74,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1361,plain,
    ( ~ r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9))
    | ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_12,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1403,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9))
    | ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1406,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9))
    | ~ v1_xboole_0(sK9) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1483,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8))
    | ~ v1_xboole_0(k2_zfmisc_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1486,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8))
    | ~ v1_xboole_0(sK8) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_705,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1496,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK9)
    | sK9 != X0 ),
    inference(instantiation,[status(thm)],[c_705])).

cnf(c_1503,plain,
    ( v1_xboole_0(sK9)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK9 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1496])).

cnf(c_1719,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK8)
    | sK8 != X0 ),
    inference(instantiation,[status(thm)],[c_705])).

cnf(c_1726,plain,
    ( v1_xboole_0(sK8)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK8 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1719])).

cnf(c_1749,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK6,sK7))
    | ~ v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1752,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK6,sK7))
    | ~ v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2359,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK6)
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_705])).

cnf(c_2366,plain,
    ( v1_xboole_0(sK6)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2359])).

cnf(c_2374,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK7)
    | sK7 != X0 ),
    inference(instantiation,[status(thm)],[c_705])).

cnf(c_2381,plain,
    ( v1_xboole_0(sK7)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK7 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2374])).

cnf(c_5383,plain,
    ( k4_tarski(k4_tarski(k4_tarski(sK1(sK6,sK7,sK8,sK9,sK5),sK2(sK6,sK7,sK8,sK9,sK5)),sK3(sK6,sK7,sK8,sK9,sK5)),sK4(sK6,sK7,sK8,sK9,sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4574,c_21,c_55,c_58,c_71,c_74,c_1361,c_1403,c_1406,c_1483,c_1486,c_1503,c_1726,c_1749,c_1752,c_2366,c_2381])).

cnf(c_20,negated_conjecture,
    ( ~ r2_hidden(X0,sK6)
    | ~ r2_hidden(X1,sK7)
    | ~ r2_hidden(X2,sK8)
    | ~ r2_hidden(X3,sK9)
    | k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) != sK5 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1167,plain,
    ( k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) != sK5
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top
    | r2_hidden(X2,sK8) != iProver_top
    | r2_hidden(X3,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5388,plain,
    ( r2_hidden(sK4(sK6,sK7,sK8,sK9,sK5),sK9) != iProver_top
    | r2_hidden(sK3(sK6,sK7,sK8,sK9,sK5),sK8) != iProver_top
    | r2_hidden(sK2(sK6,sK7,sK8,sK9,sK5),sK7) != iProver_top
    | r2_hidden(sK1(sK6,sK7,sK8,sK9,sK5),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5383,c_1167])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | m1_subset_1(sK4(X1,X2,X3,X4,X0),X4)
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1171,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X0),X3)) != iProver_top
    | m1_subset_1(sK4(X2,X1,X0,X3,X4),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4565,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | sK8 = k1_xboole_0
    | sK9 = k1_xboole_0
    | m1_subset_1(sK4(sK6,sK7,sK8,sK9,sK5),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_1412,c_1171])).

cnf(c_5376,plain,
    ( m1_subset_1(sK4(sK6,sK7,sK8,sK9,sK5),sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4565,c_21,c_55,c_58,c_71,c_74,c_1361,c_1403,c_1406,c_1483,c_1486,c_1503,c_1726,c_1749,c_1752,c_2366,c_2381])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1173,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5381,plain,
    ( r2_hidden(sK4(sK6,sK7,sK8,sK9,sK5),sK9) = iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_5376,c_1173])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | m1_subset_1(sK3(X1,X2,X3,X4,X0),X3)
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1170,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X0),X3)) != iProver_top
    | m1_subset_1(sK3(X2,X1,X0,X3,X4),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3954,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | sK8 = k1_xboole_0
    | sK9 = k1_xboole_0
    | m1_subset_1(sK3(sK6,sK7,sK8,sK9,sK5),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1412,c_1170])).

cnf(c_5132,plain,
    ( m1_subset_1(sK3(sK6,sK7,sK8,sK9,sK5),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3954,c_21,c_55,c_58,c_71,c_74,c_1361,c_1403,c_1406,c_1483,c_1486,c_1503,c_1726,c_1749,c_1752,c_2366,c_2381])).

cnf(c_5137,plain,
    ( r2_hidden(sK3(sK6,sK7,sK8,sK9,sK5),sK8) = iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_5132,c_1173])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | m1_subset_1(sK2(X1,X2,X3,X4,X0),X2)
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1169,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X0),X3)) != iProver_top
    | m1_subset_1(sK2(X2,X1,X0,X3,X4),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2406,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | sK8 = k1_xboole_0
    | sK9 = k1_xboole_0
    | m1_subset_1(sK2(sK6,sK7,sK8,sK9,sK5),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1412,c_1169])).

cnf(c_3054,plain,
    ( m1_subset_1(sK2(sK6,sK7,sK8,sK9,sK5),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2406,c_21,c_55,c_58,c_71,c_74,c_1361,c_1403,c_1406,c_1483,c_1486,c_1503,c_1726,c_1749,c_1752,c_2366,c_2381])).

cnf(c_3059,plain,
    ( r2_hidden(sK2(sK6,sK7,sK8,sK9,sK5),sK7) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3054,c_1173])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | m1_subset_1(sK1(X1,X2,X3,X4,X0),X1)
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1168,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X0),X3)) != iProver_top
    | m1_subset_1(sK1(X2,X1,X0,X3,X4),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1661,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | sK8 = k1_xboole_0
    | sK9 = k1_xboole_0
    | m1_subset_1(sK1(sK6,sK7,sK8,sK9,sK5),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1412,c_1168])).

cnf(c_2088,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | m1_subset_1(sK1(sK6,sK7,sK8,sK9,sK5),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1661,c_21,c_55,c_58,c_71,c_74,c_1361,c_1403,c_1406,c_1486,c_1503,c_1726])).

cnf(c_2768,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0
    | r2_hidden(sK1(sK6,sK7,sK8,sK9,sK5),sK6) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2088,c_1173])).

cnf(c_1753,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK6,sK7)) = iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1752])).

cnf(c_1750,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK6,sK7)) = iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1749])).

cnf(c_1487,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1486])).

cnf(c_1484,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1483])).

cnf(c_1407,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9)) = iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1406])).

cnf(c_1404,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1403])).

cnf(c_1362,plain,
    ( r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9)) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1361])).

cnf(c_22,plain,
    ( r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5388,c_5381,c_5137,c_3059,c_2768,c_2381,c_2366,c_1753,c_1752,c_1750,c_1749,c_1487,c_1484,c_1483,c_1407,c_1404,c_1403,c_1362,c_1361,c_74,c_71,c_58,c_55,c_22,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:47:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.18/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.02  
% 2.18/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.18/1.02  
% 2.18/1.02  ------  iProver source info
% 2.18/1.02  
% 2.18/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.18/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.18/1.02  git: non_committed_changes: false
% 2.18/1.02  git: last_make_outside_of_git: false
% 2.18/1.02  
% 2.18/1.02  ------ 
% 2.18/1.02  
% 2.18/1.02  ------ Input Options
% 2.18/1.02  
% 2.18/1.02  --out_options                           all
% 2.18/1.02  --tptp_safe_out                         true
% 2.18/1.02  --problem_path                          ""
% 2.18/1.02  --include_path                          ""
% 2.18/1.02  --clausifier                            res/vclausify_rel
% 2.18/1.02  --clausifier_options                    --mode clausify
% 2.18/1.02  --stdin                                 false
% 2.18/1.02  --stats_out                             all
% 2.18/1.02  
% 2.18/1.02  ------ General Options
% 2.18/1.02  
% 2.18/1.02  --fof                                   false
% 2.18/1.02  --time_out_real                         305.
% 2.18/1.02  --time_out_virtual                      -1.
% 2.18/1.02  --symbol_type_check                     false
% 2.18/1.02  --clausify_out                          false
% 2.18/1.02  --sig_cnt_out                           false
% 2.18/1.02  --trig_cnt_out                          false
% 2.18/1.02  --trig_cnt_out_tolerance                1.
% 2.18/1.02  --trig_cnt_out_sk_spl                   false
% 2.18/1.02  --abstr_cl_out                          false
% 2.18/1.02  
% 2.18/1.02  ------ Global Options
% 2.18/1.02  
% 2.18/1.02  --schedule                              default
% 2.18/1.02  --add_important_lit                     false
% 2.18/1.02  --prop_solver_per_cl                    1000
% 2.18/1.02  --min_unsat_core                        false
% 2.18/1.02  --soft_assumptions                      false
% 2.18/1.02  --soft_lemma_size                       3
% 2.18/1.02  --prop_impl_unit_size                   0
% 2.18/1.02  --prop_impl_unit                        []
% 2.18/1.02  --share_sel_clauses                     true
% 2.18/1.02  --reset_solvers                         false
% 2.18/1.02  --bc_imp_inh                            [conj_cone]
% 2.18/1.02  --conj_cone_tolerance                   3.
% 2.18/1.02  --extra_neg_conj                        none
% 2.18/1.02  --large_theory_mode                     true
% 2.18/1.02  --prolific_symb_bound                   200
% 2.18/1.02  --lt_threshold                          2000
% 2.18/1.02  --clause_weak_htbl                      true
% 2.18/1.02  --gc_record_bc_elim                     false
% 2.18/1.02  
% 2.18/1.02  ------ Preprocessing Options
% 2.18/1.02  
% 2.18/1.02  --preprocessing_flag                    true
% 2.18/1.02  --time_out_prep_mult                    0.1
% 2.18/1.02  --splitting_mode                        input
% 2.18/1.02  --splitting_grd                         true
% 2.18/1.02  --splitting_cvd                         false
% 2.18/1.02  --splitting_cvd_svl                     false
% 2.18/1.02  --splitting_nvd                         32
% 2.18/1.02  --sub_typing                            true
% 2.18/1.02  --prep_gs_sim                           true
% 2.18/1.02  --prep_unflatten                        true
% 2.18/1.02  --prep_res_sim                          true
% 2.18/1.02  --prep_upred                            true
% 2.18/1.02  --prep_sem_filter                       exhaustive
% 2.18/1.02  --prep_sem_filter_out                   false
% 2.18/1.02  --pred_elim                             true
% 2.18/1.02  --res_sim_input                         true
% 2.18/1.02  --eq_ax_congr_red                       true
% 2.18/1.02  --pure_diseq_elim                       true
% 2.18/1.02  --brand_transform                       false
% 2.18/1.02  --non_eq_to_eq                          false
% 2.18/1.02  --prep_def_merge                        true
% 2.18/1.02  --prep_def_merge_prop_impl              false
% 2.18/1.02  --prep_def_merge_mbd                    true
% 2.18/1.02  --prep_def_merge_tr_red                 false
% 2.18/1.02  --prep_def_merge_tr_cl                  false
% 2.18/1.02  --smt_preprocessing                     true
% 2.18/1.02  --smt_ac_axioms                         fast
% 2.18/1.02  --preprocessed_out                      false
% 2.18/1.02  --preprocessed_stats                    false
% 2.18/1.02  
% 2.18/1.02  ------ Abstraction refinement Options
% 2.18/1.02  
% 2.18/1.02  --abstr_ref                             []
% 2.18/1.02  --abstr_ref_prep                        false
% 2.18/1.02  --abstr_ref_until_sat                   false
% 2.18/1.02  --abstr_ref_sig_restrict                funpre
% 2.18/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.18/1.02  --abstr_ref_under                       []
% 2.18/1.02  
% 2.18/1.02  ------ SAT Options
% 2.18/1.02  
% 2.18/1.02  --sat_mode                              false
% 2.18/1.02  --sat_fm_restart_options                ""
% 2.18/1.02  --sat_gr_def                            false
% 2.18/1.02  --sat_epr_types                         true
% 2.18/1.02  --sat_non_cyclic_types                  false
% 2.18/1.02  --sat_finite_models                     false
% 2.18/1.02  --sat_fm_lemmas                         false
% 2.18/1.02  --sat_fm_prep                           false
% 2.18/1.02  --sat_fm_uc_incr                        true
% 2.18/1.02  --sat_out_model                         small
% 2.18/1.02  --sat_out_clauses                       false
% 2.18/1.02  
% 2.18/1.02  ------ QBF Options
% 2.18/1.02  
% 2.18/1.02  --qbf_mode                              false
% 2.18/1.02  --qbf_elim_univ                         false
% 2.18/1.02  --qbf_dom_inst                          none
% 2.18/1.02  --qbf_dom_pre_inst                      false
% 2.18/1.02  --qbf_sk_in                             false
% 2.18/1.02  --qbf_pred_elim                         true
% 2.18/1.02  --qbf_split                             512
% 2.18/1.02  
% 2.18/1.02  ------ BMC1 Options
% 2.18/1.02  
% 2.18/1.02  --bmc1_incremental                      false
% 2.18/1.02  --bmc1_axioms                           reachable_all
% 2.18/1.02  --bmc1_min_bound                        0
% 2.18/1.02  --bmc1_max_bound                        -1
% 2.18/1.02  --bmc1_max_bound_default                -1
% 2.18/1.02  --bmc1_symbol_reachability              true
% 2.18/1.02  --bmc1_property_lemmas                  false
% 2.18/1.02  --bmc1_k_induction                      false
% 2.18/1.02  --bmc1_non_equiv_states                 false
% 2.18/1.02  --bmc1_deadlock                         false
% 2.18/1.02  --bmc1_ucm                              false
% 2.18/1.02  --bmc1_add_unsat_core                   none
% 2.18/1.02  --bmc1_unsat_core_children              false
% 2.18/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.18/1.02  --bmc1_out_stat                         full
% 2.18/1.02  --bmc1_ground_init                      false
% 2.18/1.02  --bmc1_pre_inst_next_state              false
% 2.18/1.02  --bmc1_pre_inst_state                   false
% 2.18/1.02  --bmc1_pre_inst_reach_state             false
% 2.18/1.02  --bmc1_out_unsat_core                   false
% 2.18/1.02  --bmc1_aig_witness_out                  false
% 2.18/1.02  --bmc1_verbose                          false
% 2.18/1.02  --bmc1_dump_clauses_tptp                false
% 2.18/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.18/1.02  --bmc1_dump_file                        -
% 2.18/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.18/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.18/1.02  --bmc1_ucm_extend_mode                  1
% 2.18/1.02  --bmc1_ucm_init_mode                    2
% 2.18/1.02  --bmc1_ucm_cone_mode                    none
% 2.18/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.18/1.02  --bmc1_ucm_relax_model                  4
% 2.18/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.18/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.18/1.02  --bmc1_ucm_layered_model                none
% 2.18/1.02  --bmc1_ucm_max_lemma_size               10
% 2.18/1.02  
% 2.18/1.02  ------ AIG Options
% 2.18/1.02  
% 2.18/1.02  --aig_mode                              false
% 2.18/1.02  
% 2.18/1.02  ------ Instantiation Options
% 2.18/1.02  
% 2.18/1.02  --instantiation_flag                    true
% 2.18/1.02  --inst_sos_flag                         false
% 2.18/1.02  --inst_sos_phase                        true
% 2.18/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.18/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.18/1.02  --inst_lit_sel_side                     num_symb
% 2.18/1.02  --inst_solver_per_active                1400
% 2.18/1.02  --inst_solver_calls_frac                1.
% 2.18/1.02  --inst_passive_queue_type               priority_queues
% 2.18/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.18/1.02  --inst_passive_queues_freq              [25;2]
% 2.18/1.02  --inst_dismatching                      true
% 2.18/1.02  --inst_eager_unprocessed_to_passive     true
% 2.18/1.02  --inst_prop_sim_given                   true
% 2.18/1.02  --inst_prop_sim_new                     false
% 2.18/1.02  --inst_subs_new                         false
% 2.18/1.02  --inst_eq_res_simp                      false
% 2.18/1.02  --inst_subs_given                       false
% 2.18/1.02  --inst_orphan_elimination               true
% 2.18/1.02  --inst_learning_loop_flag               true
% 2.18/1.02  --inst_learning_start                   3000
% 2.18/1.02  --inst_learning_factor                  2
% 2.18/1.02  --inst_start_prop_sim_after_learn       3
% 2.18/1.02  --inst_sel_renew                        solver
% 2.18/1.02  --inst_lit_activity_flag                true
% 2.18/1.02  --inst_restr_to_given                   false
% 2.18/1.02  --inst_activity_threshold               500
% 2.18/1.02  --inst_out_proof                        true
% 2.18/1.02  
% 2.18/1.02  ------ Resolution Options
% 2.18/1.02  
% 2.18/1.02  --resolution_flag                       true
% 2.18/1.02  --res_lit_sel                           adaptive
% 2.18/1.02  --res_lit_sel_side                      none
% 2.18/1.02  --res_ordering                          kbo
% 2.18/1.02  --res_to_prop_solver                    active
% 2.18/1.02  --res_prop_simpl_new                    false
% 2.18/1.02  --res_prop_simpl_given                  true
% 2.18/1.02  --res_passive_queue_type                priority_queues
% 2.18/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.18/1.02  --res_passive_queues_freq               [15;5]
% 2.18/1.02  --res_forward_subs                      full
% 2.18/1.02  --res_backward_subs                     full
% 2.18/1.02  --res_forward_subs_resolution           true
% 2.18/1.02  --res_backward_subs_resolution          true
% 2.18/1.02  --res_orphan_elimination                true
% 2.18/1.02  --res_time_limit                        2.
% 2.18/1.02  --res_out_proof                         true
% 2.18/1.02  
% 2.18/1.02  ------ Superposition Options
% 2.18/1.02  
% 2.18/1.02  --superposition_flag                    true
% 2.18/1.02  --sup_passive_queue_type                priority_queues
% 2.18/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.18/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.18/1.02  --demod_completeness_check              fast
% 2.18/1.02  --demod_use_ground                      true
% 2.18/1.02  --sup_to_prop_solver                    passive
% 2.18/1.02  --sup_prop_simpl_new                    true
% 2.18/1.02  --sup_prop_simpl_given                  true
% 2.18/1.02  --sup_fun_splitting                     false
% 2.18/1.02  --sup_smt_interval                      50000
% 2.18/1.02  
% 2.18/1.02  ------ Superposition Simplification Setup
% 2.18/1.02  
% 2.18/1.02  --sup_indices_passive                   []
% 2.18/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.18/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.02  --sup_full_bw                           [BwDemod]
% 2.18/1.02  --sup_immed_triv                        [TrivRules]
% 2.18/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.18/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.02  --sup_immed_bw_main                     []
% 2.18/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.18/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.02  
% 2.18/1.02  ------ Combination Options
% 2.18/1.02  
% 2.18/1.02  --comb_res_mult                         3
% 2.18/1.02  --comb_sup_mult                         2
% 2.18/1.02  --comb_inst_mult                        10
% 2.18/1.02  
% 2.18/1.02  ------ Debug Options
% 2.18/1.02  
% 2.18/1.02  --dbg_backtrace                         false
% 2.18/1.02  --dbg_dump_prop_clauses                 false
% 2.18/1.02  --dbg_dump_prop_clauses_file            -
% 2.18/1.02  --dbg_out_stat                          false
% 2.18/1.02  ------ Parsing...
% 2.18/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.18/1.02  
% 2.18/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.18/1.02  
% 2.18/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.18/1.02  
% 2.18/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.18/1.02  ------ Proving...
% 2.18/1.02  ------ Problem Properties 
% 2.18/1.02  
% 2.18/1.02  
% 2.18/1.02  clauses                                 21
% 2.18/1.02  conjectures                             2
% 2.18/1.02  EPR                                     7
% 2.18/1.02  Horn                                    13
% 2.18/1.02  unary                                   3
% 2.18/1.02  binary                                  8
% 2.18/1.02  lits                                    66
% 2.18/1.02  lits eq                                 26
% 2.18/1.02  fd_pure                                 0
% 2.18/1.02  fd_pseudo                               0
% 2.18/1.02  fd_cond                                 4
% 2.18/1.02  fd_pseudo_cond                          1
% 2.18/1.02  AC symbols                              0
% 2.18/1.02  
% 2.18/1.02  ------ Schedule dynamic 5 is on 
% 2.18/1.02  
% 2.18/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.18/1.02  
% 2.18/1.02  
% 2.18/1.02  ------ 
% 2.18/1.02  Current options:
% 2.18/1.02  ------ 
% 2.18/1.02  
% 2.18/1.02  ------ Input Options
% 2.18/1.02  
% 2.18/1.02  --out_options                           all
% 2.18/1.02  --tptp_safe_out                         true
% 2.18/1.02  --problem_path                          ""
% 2.18/1.02  --include_path                          ""
% 2.18/1.02  --clausifier                            res/vclausify_rel
% 2.18/1.02  --clausifier_options                    --mode clausify
% 2.18/1.02  --stdin                                 false
% 2.18/1.02  --stats_out                             all
% 2.18/1.02  
% 2.18/1.02  ------ General Options
% 2.18/1.02  
% 2.18/1.02  --fof                                   false
% 2.18/1.02  --time_out_real                         305.
% 2.18/1.02  --time_out_virtual                      -1.
% 2.18/1.02  --symbol_type_check                     false
% 2.18/1.02  --clausify_out                          false
% 2.18/1.02  --sig_cnt_out                           false
% 2.18/1.02  --trig_cnt_out                          false
% 2.18/1.02  --trig_cnt_out_tolerance                1.
% 2.18/1.02  --trig_cnt_out_sk_spl                   false
% 2.18/1.02  --abstr_cl_out                          false
% 2.18/1.02  
% 2.18/1.02  ------ Global Options
% 2.18/1.02  
% 2.18/1.02  --schedule                              default
% 2.18/1.02  --add_important_lit                     false
% 2.18/1.02  --prop_solver_per_cl                    1000
% 2.18/1.02  --min_unsat_core                        false
% 2.18/1.02  --soft_assumptions                      false
% 2.18/1.02  --soft_lemma_size                       3
% 2.18/1.02  --prop_impl_unit_size                   0
% 2.18/1.02  --prop_impl_unit                        []
% 2.18/1.02  --share_sel_clauses                     true
% 2.18/1.02  --reset_solvers                         false
% 2.18/1.02  --bc_imp_inh                            [conj_cone]
% 2.18/1.02  --conj_cone_tolerance                   3.
% 2.18/1.02  --extra_neg_conj                        none
% 2.18/1.02  --large_theory_mode                     true
% 2.18/1.02  --prolific_symb_bound                   200
% 2.18/1.02  --lt_threshold                          2000
% 2.18/1.02  --clause_weak_htbl                      true
% 2.18/1.02  --gc_record_bc_elim                     false
% 2.18/1.02  
% 2.18/1.02  ------ Preprocessing Options
% 2.18/1.02  
% 2.18/1.02  --preprocessing_flag                    true
% 2.18/1.02  --time_out_prep_mult                    0.1
% 2.18/1.02  --splitting_mode                        input
% 2.18/1.02  --splitting_grd                         true
% 2.18/1.02  --splitting_cvd                         false
% 2.18/1.02  --splitting_cvd_svl                     false
% 2.18/1.02  --splitting_nvd                         32
% 2.18/1.02  --sub_typing                            true
% 2.18/1.02  --prep_gs_sim                           true
% 2.18/1.02  --prep_unflatten                        true
% 2.18/1.02  --prep_res_sim                          true
% 2.18/1.02  --prep_upred                            true
% 2.18/1.02  --prep_sem_filter                       exhaustive
% 2.18/1.02  --prep_sem_filter_out                   false
% 2.18/1.02  --pred_elim                             true
% 2.18/1.02  --res_sim_input                         true
% 2.18/1.02  --eq_ax_congr_red                       true
% 2.18/1.02  --pure_diseq_elim                       true
% 2.18/1.02  --brand_transform                       false
% 2.18/1.02  --non_eq_to_eq                          false
% 2.18/1.02  --prep_def_merge                        true
% 2.18/1.02  --prep_def_merge_prop_impl              false
% 2.18/1.02  --prep_def_merge_mbd                    true
% 2.18/1.02  --prep_def_merge_tr_red                 false
% 2.18/1.02  --prep_def_merge_tr_cl                  false
% 2.18/1.02  --smt_preprocessing                     true
% 2.18/1.02  --smt_ac_axioms                         fast
% 2.18/1.02  --preprocessed_out                      false
% 2.18/1.02  --preprocessed_stats                    false
% 2.18/1.02  
% 2.18/1.02  ------ Abstraction refinement Options
% 2.18/1.02  
% 2.18/1.02  --abstr_ref                             []
% 2.18/1.02  --abstr_ref_prep                        false
% 2.18/1.02  --abstr_ref_until_sat                   false
% 2.18/1.02  --abstr_ref_sig_restrict                funpre
% 2.18/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.18/1.02  --abstr_ref_under                       []
% 2.18/1.02  
% 2.18/1.02  ------ SAT Options
% 2.18/1.02  
% 2.18/1.02  --sat_mode                              false
% 2.18/1.02  --sat_fm_restart_options                ""
% 2.18/1.02  --sat_gr_def                            false
% 2.18/1.02  --sat_epr_types                         true
% 2.18/1.02  --sat_non_cyclic_types                  false
% 2.18/1.02  --sat_finite_models                     false
% 2.18/1.02  --sat_fm_lemmas                         false
% 2.18/1.02  --sat_fm_prep                           false
% 2.18/1.02  --sat_fm_uc_incr                        true
% 2.18/1.02  --sat_out_model                         small
% 2.18/1.02  --sat_out_clauses                       false
% 2.18/1.02  
% 2.18/1.02  ------ QBF Options
% 2.18/1.02  
% 2.18/1.02  --qbf_mode                              false
% 2.18/1.02  --qbf_elim_univ                         false
% 2.18/1.02  --qbf_dom_inst                          none
% 2.18/1.02  --qbf_dom_pre_inst                      false
% 2.18/1.02  --qbf_sk_in                             false
% 2.18/1.02  --qbf_pred_elim                         true
% 2.18/1.02  --qbf_split                             512
% 2.18/1.02  
% 2.18/1.02  ------ BMC1 Options
% 2.18/1.02  
% 2.18/1.02  --bmc1_incremental                      false
% 2.18/1.02  --bmc1_axioms                           reachable_all
% 2.18/1.02  --bmc1_min_bound                        0
% 2.18/1.02  --bmc1_max_bound                        -1
% 2.18/1.02  --bmc1_max_bound_default                -1
% 2.18/1.02  --bmc1_symbol_reachability              true
% 2.18/1.02  --bmc1_property_lemmas                  false
% 2.18/1.02  --bmc1_k_induction                      false
% 2.18/1.02  --bmc1_non_equiv_states                 false
% 2.18/1.02  --bmc1_deadlock                         false
% 2.18/1.02  --bmc1_ucm                              false
% 2.18/1.02  --bmc1_add_unsat_core                   none
% 2.18/1.02  --bmc1_unsat_core_children              false
% 2.18/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.18/1.02  --bmc1_out_stat                         full
% 2.18/1.02  --bmc1_ground_init                      false
% 2.18/1.02  --bmc1_pre_inst_next_state              false
% 2.18/1.02  --bmc1_pre_inst_state                   false
% 2.18/1.02  --bmc1_pre_inst_reach_state             false
% 2.18/1.02  --bmc1_out_unsat_core                   false
% 2.18/1.02  --bmc1_aig_witness_out                  false
% 2.18/1.02  --bmc1_verbose                          false
% 2.18/1.02  --bmc1_dump_clauses_tptp                false
% 2.18/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.18/1.02  --bmc1_dump_file                        -
% 2.18/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.18/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.18/1.02  --bmc1_ucm_extend_mode                  1
% 2.18/1.02  --bmc1_ucm_init_mode                    2
% 2.18/1.02  --bmc1_ucm_cone_mode                    none
% 2.18/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.18/1.02  --bmc1_ucm_relax_model                  4
% 2.18/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.18/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.18/1.02  --bmc1_ucm_layered_model                none
% 2.18/1.02  --bmc1_ucm_max_lemma_size               10
% 2.18/1.02  
% 2.18/1.02  ------ AIG Options
% 2.18/1.02  
% 2.18/1.02  --aig_mode                              false
% 2.18/1.02  
% 2.18/1.02  ------ Instantiation Options
% 2.18/1.02  
% 2.18/1.02  --instantiation_flag                    true
% 2.18/1.02  --inst_sos_flag                         false
% 2.18/1.02  --inst_sos_phase                        true
% 2.18/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.18/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.18/1.02  --inst_lit_sel_side                     none
% 2.18/1.02  --inst_solver_per_active                1400
% 2.18/1.02  --inst_solver_calls_frac                1.
% 2.18/1.02  --inst_passive_queue_type               priority_queues
% 2.18/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.18/1.02  --inst_passive_queues_freq              [25;2]
% 2.18/1.02  --inst_dismatching                      true
% 2.18/1.02  --inst_eager_unprocessed_to_passive     true
% 2.18/1.02  --inst_prop_sim_given                   true
% 2.18/1.02  --inst_prop_sim_new                     false
% 2.18/1.02  --inst_subs_new                         false
% 2.18/1.02  --inst_eq_res_simp                      false
% 2.18/1.02  --inst_subs_given                       false
% 2.18/1.02  --inst_orphan_elimination               true
% 2.18/1.02  --inst_learning_loop_flag               true
% 2.18/1.02  --inst_learning_start                   3000
% 2.18/1.02  --inst_learning_factor                  2
% 2.18/1.02  --inst_start_prop_sim_after_learn       3
% 2.18/1.02  --inst_sel_renew                        solver
% 2.18/1.02  --inst_lit_activity_flag                true
% 2.18/1.02  --inst_restr_to_given                   false
% 2.18/1.02  --inst_activity_threshold               500
% 2.18/1.02  --inst_out_proof                        true
% 2.18/1.02  
% 2.18/1.02  ------ Resolution Options
% 2.18/1.02  
% 2.18/1.02  --resolution_flag                       false
% 2.18/1.02  --res_lit_sel                           adaptive
% 2.18/1.02  --res_lit_sel_side                      none
% 2.18/1.02  --res_ordering                          kbo
% 2.18/1.02  --res_to_prop_solver                    active
% 2.18/1.02  --res_prop_simpl_new                    false
% 2.18/1.02  --res_prop_simpl_given                  true
% 2.18/1.02  --res_passive_queue_type                priority_queues
% 2.18/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.18/1.02  --res_passive_queues_freq               [15;5]
% 2.18/1.02  --res_forward_subs                      full
% 2.18/1.02  --res_backward_subs                     full
% 2.18/1.02  --res_forward_subs_resolution           true
% 2.18/1.02  --res_backward_subs_resolution          true
% 2.18/1.02  --res_orphan_elimination                true
% 2.18/1.02  --res_time_limit                        2.
% 2.18/1.02  --res_out_proof                         true
% 2.18/1.02  
% 2.18/1.02  ------ Superposition Options
% 2.18/1.02  
% 2.18/1.02  --superposition_flag                    true
% 2.18/1.02  --sup_passive_queue_type                priority_queues
% 2.18/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.18/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.18/1.02  --demod_completeness_check              fast
% 2.18/1.02  --demod_use_ground                      true
% 2.18/1.02  --sup_to_prop_solver                    passive
% 2.18/1.02  --sup_prop_simpl_new                    true
% 2.18/1.02  --sup_prop_simpl_given                  true
% 2.18/1.02  --sup_fun_splitting                     false
% 2.18/1.02  --sup_smt_interval                      50000
% 2.18/1.02  
% 2.18/1.02  ------ Superposition Simplification Setup
% 2.18/1.02  
% 2.18/1.02  --sup_indices_passive                   []
% 2.18/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.18/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.02  --sup_full_bw                           [BwDemod]
% 2.18/1.02  --sup_immed_triv                        [TrivRules]
% 2.18/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.18/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.02  --sup_immed_bw_main                     []
% 2.18/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.18/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.02  
% 2.18/1.02  ------ Combination Options
% 2.18/1.02  
% 2.18/1.02  --comb_res_mult                         3
% 2.18/1.02  --comb_sup_mult                         2
% 2.18/1.02  --comb_inst_mult                        10
% 2.18/1.02  
% 2.18/1.02  ------ Debug Options
% 2.18/1.02  
% 2.18/1.02  --dbg_backtrace                         false
% 2.18/1.02  --dbg_dump_prop_clauses                 false
% 2.18/1.02  --dbg_dump_prop_clauses_file            -
% 2.18/1.02  --dbg_out_stat                          false
% 2.18/1.02  
% 2.18/1.02  
% 2.18/1.02  
% 2.18/1.02  
% 2.18/1.02  ------ Proving...
% 2.18/1.02  
% 2.18/1.02  
% 2.18/1.02  % SZS status Theorem for theBenchmark.p
% 2.18/1.02  
% 2.18/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.18/1.02  
% 2.18/1.02  fof(f14,conjecture,(
% 2.18/1.02    ! [X0,X1,X2,X3,X4] : ~(! [X5,X6,X7,X8] : ~(k4_mcart_1(X5,X6,X7,X8) = X0 & r2_hidden(X8,X4) & r2_hidden(X7,X3) & r2_hidden(X6,X2) & r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 2.18/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f15,negated_conjecture,(
% 2.18/1.02    ~! [X0,X1,X2,X3,X4] : ~(! [X5,X6,X7,X8] : ~(k4_mcart_1(X5,X6,X7,X8) = X0 & r2_hidden(X8,X4) & r2_hidden(X7,X3) & r2_hidden(X6,X2) & r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 2.18/1.02    inference(negated_conjecture,[],[f14])).
% 2.18/1.02  
% 2.18/1.02  fof(f28,plain,(
% 2.18/1.02    ? [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : (k4_mcart_1(X5,X6,X7,X8) != X0 | ~r2_hidden(X8,X4) | ~r2_hidden(X7,X3) | ~r2_hidden(X6,X2) | ~r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 2.18/1.02    inference(ennf_transformation,[],[f15])).
% 2.18/1.02  
% 2.18/1.02  fof(f39,plain,(
% 2.18/1.02    ? [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : (k4_mcart_1(X5,X6,X7,X8) != X0 | ~r2_hidden(X8,X4) | ~r2_hidden(X7,X3) | ~r2_hidden(X6,X2) | ~r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4))) => (! [X8,X7,X6,X5] : (k4_mcart_1(X5,X6,X7,X8) != sK5 | ~r2_hidden(X8,sK9) | ~r2_hidden(X7,sK8) | ~r2_hidden(X6,sK7) | ~r2_hidden(X5,sK6)) & r2_hidden(sK5,k4_zfmisc_1(sK6,sK7,sK8,sK9)))),
% 2.18/1.02    introduced(choice_axiom,[])).
% 2.18/1.02  
% 2.18/1.02  fof(f40,plain,(
% 2.18/1.02    ! [X5,X6,X7,X8] : (k4_mcart_1(X5,X6,X7,X8) != sK5 | ~r2_hidden(X8,sK9) | ~r2_hidden(X7,sK8) | ~r2_hidden(X6,sK7) | ~r2_hidden(X5,sK6)) & r2_hidden(sK5,k4_zfmisc_1(sK6,sK7,sK8,sK9))),
% 2.18/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f28,f39])).
% 2.18/1.02  
% 2.18/1.02  fof(f63,plain,(
% 2.18/1.02    r2_hidden(sK5,k4_zfmisc_1(sK6,sK7,sK8,sK9))),
% 2.18/1.02    inference(cnf_transformation,[],[f40])).
% 2.18/1.02  
% 2.18/1.02  fof(f13,axiom,(
% 2.18/1.02    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 2.18/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f62,plain,(
% 2.18/1.02    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.18/1.02    inference(cnf_transformation,[],[f13])).
% 2.18/1.02  
% 2.18/1.02  fof(f71,plain,(
% 2.18/1.02    r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9))),
% 2.18/1.02    inference(definition_unfolding,[],[f63,f62])).
% 2.18/1.02  
% 2.18/1.02  fof(f9,axiom,(
% 2.18/1.02    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.18/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f24,plain,(
% 2.18/1.02    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.18/1.02    inference(ennf_transformation,[],[f9])).
% 2.18/1.02  
% 2.18/1.02  fof(f54,plain,(
% 2.18/1.02    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.18/1.02    inference(cnf_transformation,[],[f24])).
% 2.18/1.02  
% 2.18/1.02  fof(f11,axiom,(
% 2.18/1.02    ! [X0,X1,X2,X3] : ~(? [X4] : (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => ! [X8] : (m1_subset_1(X8,X3) => k4_mcart_1(X5,X6,X7,X8) != X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.18/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f27,plain,(
% 2.18/1.02    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.18/1.02    inference(ennf_transformation,[],[f11])).
% 2.18/1.02  
% 2.18/1.02  fof(f37,plain,(
% 2.18/1.02    ( ! [X6,X7,X5] : (! [X4,X3,X2,X1,X0] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) => (k4_mcart_1(X5,X6,X7,sK4(X0,X1,X2,X3,X4)) = X4 & m1_subset_1(sK4(X0,X1,X2,X3,X4),X3)))) )),
% 2.18/1.02    introduced(choice_axiom,[])).
% 2.18/1.02  
% 2.18/1.02  fof(f36,plain,(
% 2.18/1.02    ( ! [X6,X5] : (! [X4,X3,X2,X1,X0] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) => (? [X8] : (k4_mcart_1(X5,X6,sK3(X0,X1,X2,X3,X4),X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(sK3(X0,X1,X2,X3,X4),X2)))) )),
% 2.18/1.02    introduced(choice_axiom,[])).
% 2.18/1.02  
% 2.18/1.02  fof(f35,plain,(
% 2.18/1.02    ( ! [X5] : (! [X4,X3,X2,X1,X0] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) => (? [X7] : (? [X8] : (k4_mcart_1(X5,sK2(X0,X1,X2,X3,X4),X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(sK2(X0,X1,X2,X3,X4),X1)))) )),
% 2.18/1.02    introduced(choice_axiom,[])).
% 2.18/1.02  
% 2.18/1.02  fof(f34,plain,(
% 2.18/1.02    ! [X4,X3,X2,X1,X0] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) => (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(sK1(X0,X1,X2,X3,X4),X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(sK1(X0,X1,X2,X3,X4),X0)))),
% 2.18/1.02    introduced(choice_axiom,[])).
% 2.18/1.02  
% 2.18/1.02  fof(f38,plain,(
% 2.18/1.02    ! [X0,X1,X2,X3] : (! [X4] : (((((k4_mcart_1(sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4),sK3(X0,X1,X2,X3,X4),sK4(X0,X1,X2,X3,X4)) = X4 & m1_subset_1(sK4(X0,X1,X2,X3,X4),X3)) & m1_subset_1(sK3(X0,X1,X2,X3,X4),X2)) & m1_subset_1(sK2(X0,X1,X2,X3,X4),X1)) & m1_subset_1(sK1(X0,X1,X2,X3,X4),X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.18/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f27,f37,f36,f35,f34])).
% 2.18/1.02  
% 2.18/1.02  fof(f60,plain,(
% 2.18/1.02    ( ! [X4,X2,X0,X3,X1] : (k4_mcart_1(sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4),sK3(X0,X1,X2,X3,X4),sK4(X0,X1,X2,X3,X4)) = X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.18/1.02    inference(cnf_transformation,[],[f38])).
% 2.18/1.02  
% 2.18/1.02  fof(f12,axiom,(
% 2.18/1.02    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)),
% 2.18/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f61,plain,(
% 2.18/1.02    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 2.18/1.02    inference(cnf_transformation,[],[f12])).
% 2.18/1.02  
% 2.18/1.02  fof(f65,plain,(
% 2.18/1.02    ( ! [X4,X2,X0,X3,X1] : (k4_tarski(k4_tarski(k4_tarski(sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4)),sK3(X0,X1,X2,X3,X4)),sK4(X0,X1,X2,X3,X4)) = X4 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.18/1.02    inference(definition_unfolding,[],[f60,f61,f62])).
% 2.18/1.02  
% 2.18/1.02  fof(f5,axiom,(
% 2.18/1.02    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.18/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f19,plain,(
% 2.18/1.02    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.18/1.02    inference(ennf_transformation,[],[f5])).
% 2.18/1.02  
% 2.18/1.02  fof(f20,plain,(
% 2.18/1.02    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.18/1.02    inference(flattening,[],[f19])).
% 2.18/1.02  
% 2.18/1.02  fof(f50,plain,(
% 2.18/1.02    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 2.18/1.02    inference(cnf_transformation,[],[f20])).
% 2.18/1.02  
% 2.18/1.02  fof(f4,axiom,(
% 2.18/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.18/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f32,plain,(
% 2.18/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.18/1.02    inference(nnf_transformation,[],[f4])).
% 2.18/1.02  
% 2.18/1.02  fof(f33,plain,(
% 2.18/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.18/1.02    inference(flattening,[],[f32])).
% 2.18/1.02  
% 2.18/1.02  fof(f47,plain,(
% 2.18/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.18/1.02    inference(cnf_transformation,[],[f33])).
% 2.18/1.02  
% 2.18/1.02  fof(f73,plain,(
% 2.18/1.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.18/1.02    inference(equality_resolution,[],[f47])).
% 2.18/1.02  
% 2.18/1.02  fof(f2,axiom,(
% 2.18/1.02    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.18/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f16,plain,(
% 2.18/1.02    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.18/1.02    inference(rectify,[],[f2])).
% 2.18/1.02  
% 2.18/1.02  fof(f43,plain,(
% 2.18/1.02    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.18/1.02    inference(cnf_transformation,[],[f16])).
% 2.18/1.02  
% 2.18/1.02  fof(f1,axiom,(
% 2.18/1.02    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.18/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f29,plain,(
% 2.18/1.02    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.18/1.02    inference(nnf_transformation,[],[f1])).
% 2.18/1.02  
% 2.18/1.02  fof(f42,plain,(
% 2.18/1.02    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.18/1.02    inference(cnf_transformation,[],[f29])).
% 2.18/1.02  
% 2.18/1.02  fof(f6,axiom,(
% 2.18/1.02    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 2.18/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f21,plain,(
% 2.18/1.02    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 2.18/1.02    inference(ennf_transformation,[],[f6])).
% 2.18/1.02  
% 2.18/1.02  fof(f51,plain,(
% 2.18/1.02    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 2.18/1.02    inference(cnf_transformation,[],[f21])).
% 2.18/1.02  
% 2.18/1.02  fof(f8,axiom,(
% 2.18/1.02    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 2.18/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f23,plain,(
% 2.18/1.02    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 2.18/1.02    inference(ennf_transformation,[],[f8])).
% 2.18/1.02  
% 2.18/1.02  fof(f53,plain,(
% 2.18/1.02    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 2.18/1.02    inference(cnf_transformation,[],[f23])).
% 2.18/1.02  
% 2.18/1.02  fof(f7,axiom,(
% 2.18/1.02    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 2.18/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f22,plain,(
% 2.18/1.02    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 2.18/1.02    inference(ennf_transformation,[],[f7])).
% 2.18/1.02  
% 2.18/1.02  fof(f52,plain,(
% 2.18/1.02    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 2.18/1.02    inference(cnf_transformation,[],[f22])).
% 2.18/1.02  
% 2.18/1.02  fof(f64,plain,(
% 2.18/1.02    ( ! [X6,X8,X7,X5] : (k4_mcart_1(X5,X6,X7,X8) != sK5 | ~r2_hidden(X8,sK9) | ~r2_hidden(X7,sK8) | ~r2_hidden(X6,sK7) | ~r2_hidden(X5,sK6)) )),
% 2.18/1.02    inference(cnf_transformation,[],[f40])).
% 2.18/1.02  
% 2.18/1.02  fof(f70,plain,(
% 2.18/1.02    ( ! [X6,X8,X7,X5] : (k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != sK5 | ~r2_hidden(X8,sK9) | ~r2_hidden(X7,sK8) | ~r2_hidden(X6,sK7) | ~r2_hidden(X5,sK6)) )),
% 2.18/1.02    inference(definition_unfolding,[],[f64,f61])).
% 2.18/1.02  
% 2.18/1.02  fof(f59,plain,(
% 2.18/1.02    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK4(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.18/1.02    inference(cnf_transformation,[],[f38])).
% 2.18/1.02  
% 2.18/1.02  fof(f66,plain,(
% 2.18/1.02    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK4(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.18/1.02    inference(definition_unfolding,[],[f59,f62])).
% 2.18/1.02  
% 2.18/1.02  fof(f10,axiom,(
% 2.18/1.02    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.18/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f25,plain,(
% 2.18/1.02    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.18/1.02    inference(ennf_transformation,[],[f10])).
% 2.18/1.02  
% 2.18/1.02  fof(f26,plain,(
% 2.18/1.02    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.18/1.02    inference(flattening,[],[f25])).
% 2.18/1.02  
% 2.18/1.02  fof(f55,plain,(
% 2.18/1.02    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.18/1.02    inference(cnf_transformation,[],[f26])).
% 2.18/1.02  
% 2.18/1.02  fof(f58,plain,(
% 2.18/1.02    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK3(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.18/1.02    inference(cnf_transformation,[],[f38])).
% 2.18/1.02  
% 2.18/1.02  fof(f67,plain,(
% 2.18/1.02    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK3(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.18/1.02    inference(definition_unfolding,[],[f58,f62])).
% 2.18/1.02  
% 2.18/1.02  fof(f57,plain,(
% 2.18/1.02    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK2(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.18/1.02    inference(cnf_transformation,[],[f38])).
% 2.18/1.02  
% 2.18/1.02  fof(f68,plain,(
% 2.18/1.02    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK2(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.18/1.02    inference(definition_unfolding,[],[f57,f62])).
% 2.18/1.02  
% 2.18/1.02  fof(f56,plain,(
% 2.18/1.02    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK1(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.18/1.02    inference(cnf_transformation,[],[f38])).
% 2.18/1.02  
% 2.18/1.02  fof(f69,plain,(
% 2.18/1.02    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK1(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.18/1.02    inference(definition_unfolding,[],[f56,f62])).
% 2.18/1.02  
% 2.18/1.02  cnf(c_21,negated_conjecture,
% 2.18/1.02      ( r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9)) ),
% 2.18/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1166,plain,
% 2.18/1.02      ( r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9)) = iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_13,plain,
% 2.18/1.02      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.18/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1174,plain,
% 2.18/1.02      ( m1_subset_1(X0,X1) = iProver_top
% 2.18/1.02      | r2_hidden(X0,X1) != iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1412,plain,
% 2.18/1.02      ( m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9)) = iProver_top ),
% 2.18/1.02      inference(superposition,[status(thm)],[c_1166,c_1174]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_15,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 2.18/1.02      | k4_tarski(k4_tarski(k4_tarski(sK1(X1,X2,X3,X4,X0),sK2(X1,X2,X3,X4,X0)),sK3(X1,X2,X3,X4,X0)),sK4(X1,X2,X3,X4,X0)) = X0
% 2.18/1.02      | k1_xboole_0 = X4
% 2.18/1.02      | k1_xboole_0 = X3
% 2.18/1.02      | k1_xboole_0 = X2
% 2.18/1.02      | k1_xboole_0 = X1 ),
% 2.18/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1172,plain,
% 2.18/1.02      ( k4_tarski(k4_tarski(k4_tarski(sK1(X0,X1,X2,X3,X4),sK2(X0,X1,X2,X3,X4)),sK3(X0,X1,X2,X3,X4)),sK4(X0,X1,X2,X3,X4)) = X4
% 2.18/1.02      | k1_xboole_0 = X2
% 2.18/1.02      | k1_xboole_0 = X1
% 2.18/1.02      | k1_xboole_0 = X0
% 2.18/1.02      | k1_xboole_0 = X3
% 2.18/1.02      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_4574,plain,
% 2.18/1.02      ( k4_tarski(k4_tarski(k4_tarski(sK1(sK6,sK7,sK8,sK9,sK5),sK2(sK6,sK7,sK8,sK9,sK5)),sK3(sK6,sK7,sK8,sK9,sK5)),sK4(sK6,sK7,sK8,sK9,sK5)) = sK5
% 2.18/1.02      | sK6 = k1_xboole_0
% 2.18/1.02      | sK7 = k1_xboole_0
% 2.18/1.02      | sK8 = k1_xboole_0
% 2.18/1.02      | sK9 = k1_xboole_0 ),
% 2.18/1.02      inference(superposition,[status(thm)],[c_1412,c_1172]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_9,plain,
% 2.18/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | v1_xboole_0(X0) ),
% 2.18/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_55,plain,
% 2.18/1.02      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.18/1.02      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 2.18/1.02      | v1_xboole_0(k1_xboole_0) ),
% 2.18/1.02      inference(instantiation,[status(thm)],[c_9]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_8,plain,
% 2.18/1.02      ( r1_tarski(X0,X0) ),
% 2.18/1.02      inference(cnf_transformation,[],[f73]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_58,plain,
% 2.18/1.02      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.18/1.02      inference(instantiation,[status(thm)],[c_8]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_2,plain,
% 2.18/1.02      ( k3_xboole_0(X0,X0) = X0 ),
% 2.18/1.02      inference(cnf_transformation,[],[f43]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_71,plain,
% 2.18/1.02      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.18/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_0,plain,
% 2.18/1.02      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 2.18/1.02      inference(cnf_transformation,[],[f42]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_74,plain,
% 2.18/1.02      ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 2.18/1.02      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 2.18/1.02      inference(instantiation,[status(thm)],[c_0]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_10,plain,
% 2.18/1.02      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.18/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1361,plain,
% 2.18/1.02      ( ~ r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9))
% 2.18/1.02      | ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9)) ),
% 2.18/1.02      inference(instantiation,[status(thm)],[c_10]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_12,plain,
% 2.18/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 2.18/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1403,plain,
% 2.18/1.02      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9))
% 2.18/1.02      | ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) ),
% 2.18/1.02      inference(instantiation,[status(thm)],[c_12]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_11,plain,
% 2.18/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
% 2.18/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1406,plain,
% 2.18/1.02      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9))
% 2.18/1.02      | ~ v1_xboole_0(sK9) ),
% 2.18/1.02      inference(instantiation,[status(thm)],[c_11]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1483,plain,
% 2.18/1.02      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8))
% 2.18/1.02      | ~ v1_xboole_0(k2_zfmisc_1(sK6,sK7)) ),
% 2.18/1.02      inference(instantiation,[status(thm)],[c_12]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1486,plain,
% 2.18/1.02      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8))
% 2.18/1.02      | ~ v1_xboole_0(sK8) ),
% 2.18/1.02      inference(instantiation,[status(thm)],[c_11]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_705,plain,
% 2.18/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.18/1.02      theory(equality) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1496,plain,
% 2.18/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK9) | sK9 != X0 ),
% 2.18/1.02      inference(instantiation,[status(thm)],[c_705]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1503,plain,
% 2.18/1.02      ( v1_xboole_0(sK9)
% 2.18/1.02      | ~ v1_xboole_0(k1_xboole_0)
% 2.18/1.02      | sK9 != k1_xboole_0 ),
% 2.18/1.02      inference(instantiation,[status(thm)],[c_1496]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1719,plain,
% 2.18/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK8) | sK8 != X0 ),
% 2.18/1.02      inference(instantiation,[status(thm)],[c_705]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1726,plain,
% 2.18/1.02      ( v1_xboole_0(sK8)
% 2.18/1.02      | ~ v1_xboole_0(k1_xboole_0)
% 2.18/1.02      | sK8 != k1_xboole_0 ),
% 2.18/1.02      inference(instantiation,[status(thm)],[c_1719]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1749,plain,
% 2.18/1.02      ( v1_xboole_0(k2_zfmisc_1(sK6,sK7)) | ~ v1_xboole_0(sK6) ),
% 2.18/1.02      inference(instantiation,[status(thm)],[c_12]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1752,plain,
% 2.18/1.02      ( v1_xboole_0(k2_zfmisc_1(sK6,sK7)) | ~ v1_xboole_0(sK7) ),
% 2.18/1.02      inference(instantiation,[status(thm)],[c_11]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_2359,plain,
% 2.18/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK6) | sK6 != X0 ),
% 2.18/1.02      inference(instantiation,[status(thm)],[c_705]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_2366,plain,
% 2.18/1.02      ( v1_xboole_0(sK6)
% 2.18/1.02      | ~ v1_xboole_0(k1_xboole_0)
% 2.18/1.02      | sK6 != k1_xboole_0 ),
% 2.18/1.02      inference(instantiation,[status(thm)],[c_2359]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_2374,plain,
% 2.18/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK7) | sK7 != X0 ),
% 2.18/1.02      inference(instantiation,[status(thm)],[c_705]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_2381,plain,
% 2.18/1.02      ( v1_xboole_0(sK7)
% 2.18/1.02      | ~ v1_xboole_0(k1_xboole_0)
% 2.18/1.02      | sK7 != k1_xboole_0 ),
% 2.18/1.02      inference(instantiation,[status(thm)],[c_2374]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_5383,plain,
% 2.18/1.02      ( k4_tarski(k4_tarski(k4_tarski(sK1(sK6,sK7,sK8,sK9,sK5),sK2(sK6,sK7,sK8,sK9,sK5)),sK3(sK6,sK7,sK8,sK9,sK5)),sK4(sK6,sK7,sK8,sK9,sK5)) = sK5 ),
% 2.18/1.02      inference(global_propositional_subsumption,
% 2.18/1.02                [status(thm)],
% 2.18/1.02                [c_4574,c_21,c_55,c_58,c_71,c_74,c_1361,c_1403,c_1406,
% 2.18/1.02                 c_1483,c_1486,c_1503,c_1726,c_1749,c_1752,c_2366,c_2381]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_20,negated_conjecture,
% 2.18/1.02      ( ~ r2_hidden(X0,sK6)
% 2.18/1.02      | ~ r2_hidden(X1,sK7)
% 2.18/1.02      | ~ r2_hidden(X2,sK8)
% 2.18/1.02      | ~ r2_hidden(X3,sK9)
% 2.18/1.02      | k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) != sK5 ),
% 2.18/1.02      inference(cnf_transformation,[],[f70]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1167,plain,
% 2.18/1.02      ( k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) != sK5
% 2.18/1.02      | r2_hidden(X0,sK6) != iProver_top
% 2.18/1.02      | r2_hidden(X1,sK7) != iProver_top
% 2.18/1.02      | r2_hidden(X2,sK8) != iProver_top
% 2.18/1.02      | r2_hidden(X3,sK9) != iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_5388,plain,
% 2.18/1.02      ( r2_hidden(sK4(sK6,sK7,sK8,sK9,sK5),sK9) != iProver_top
% 2.18/1.02      | r2_hidden(sK3(sK6,sK7,sK8,sK9,sK5),sK8) != iProver_top
% 2.18/1.02      | r2_hidden(sK2(sK6,sK7,sK8,sK9,sK5),sK7) != iProver_top
% 2.18/1.02      | r2_hidden(sK1(sK6,sK7,sK8,sK9,sK5),sK6) != iProver_top ),
% 2.18/1.02      inference(superposition,[status(thm)],[c_5383,c_1167]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_16,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 2.18/1.02      | m1_subset_1(sK4(X1,X2,X3,X4,X0),X4)
% 2.18/1.02      | k1_xboole_0 = X4
% 2.18/1.02      | k1_xboole_0 = X3
% 2.18/1.02      | k1_xboole_0 = X2
% 2.18/1.02      | k1_xboole_0 = X1 ),
% 2.18/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1171,plain,
% 2.18/1.02      ( k1_xboole_0 = X0
% 2.18/1.02      | k1_xboole_0 = X1
% 2.18/1.02      | k1_xboole_0 = X2
% 2.18/1.02      | k1_xboole_0 = X3
% 2.18/1.02      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X0),X3)) != iProver_top
% 2.18/1.02      | m1_subset_1(sK4(X2,X1,X0,X3,X4),X3) = iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_4565,plain,
% 2.18/1.02      ( sK6 = k1_xboole_0
% 2.18/1.02      | sK7 = k1_xboole_0
% 2.18/1.02      | sK8 = k1_xboole_0
% 2.18/1.02      | sK9 = k1_xboole_0
% 2.18/1.02      | m1_subset_1(sK4(sK6,sK7,sK8,sK9,sK5),sK9) = iProver_top ),
% 2.18/1.02      inference(superposition,[status(thm)],[c_1412,c_1171]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_5376,plain,
% 2.18/1.02      ( m1_subset_1(sK4(sK6,sK7,sK8,sK9,sK5),sK9) = iProver_top ),
% 2.18/1.02      inference(global_propositional_subsumption,
% 2.18/1.02                [status(thm)],
% 2.18/1.02                [c_4565,c_21,c_55,c_58,c_71,c_74,c_1361,c_1403,c_1406,
% 2.18/1.02                 c_1483,c_1486,c_1503,c_1726,c_1749,c_1752,c_2366,c_2381]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_14,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.18/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1173,plain,
% 2.18/1.02      ( m1_subset_1(X0,X1) != iProver_top
% 2.18/1.02      | r2_hidden(X0,X1) = iProver_top
% 2.18/1.02      | v1_xboole_0(X1) = iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_5381,plain,
% 2.18/1.02      ( r2_hidden(sK4(sK6,sK7,sK8,sK9,sK5),sK9) = iProver_top
% 2.18/1.02      | v1_xboole_0(sK9) = iProver_top ),
% 2.18/1.02      inference(superposition,[status(thm)],[c_5376,c_1173]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_17,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 2.18/1.02      | m1_subset_1(sK3(X1,X2,X3,X4,X0),X3)
% 2.18/1.02      | k1_xboole_0 = X4
% 2.18/1.02      | k1_xboole_0 = X3
% 2.18/1.02      | k1_xboole_0 = X2
% 2.18/1.02      | k1_xboole_0 = X1 ),
% 2.18/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1170,plain,
% 2.18/1.02      ( k1_xboole_0 = X0
% 2.18/1.02      | k1_xboole_0 = X1
% 2.18/1.02      | k1_xboole_0 = X2
% 2.18/1.02      | k1_xboole_0 = X3
% 2.18/1.02      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X0),X3)) != iProver_top
% 2.18/1.02      | m1_subset_1(sK3(X2,X1,X0,X3,X4),X0) = iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_3954,plain,
% 2.18/1.02      ( sK6 = k1_xboole_0
% 2.18/1.02      | sK7 = k1_xboole_0
% 2.18/1.02      | sK8 = k1_xboole_0
% 2.18/1.02      | sK9 = k1_xboole_0
% 2.18/1.02      | m1_subset_1(sK3(sK6,sK7,sK8,sK9,sK5),sK8) = iProver_top ),
% 2.18/1.02      inference(superposition,[status(thm)],[c_1412,c_1170]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_5132,plain,
% 2.18/1.02      ( m1_subset_1(sK3(sK6,sK7,sK8,sK9,sK5),sK8) = iProver_top ),
% 2.18/1.02      inference(global_propositional_subsumption,
% 2.18/1.02                [status(thm)],
% 2.18/1.02                [c_3954,c_21,c_55,c_58,c_71,c_74,c_1361,c_1403,c_1406,
% 2.18/1.02                 c_1483,c_1486,c_1503,c_1726,c_1749,c_1752,c_2366,c_2381]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_5137,plain,
% 2.18/1.02      ( r2_hidden(sK3(sK6,sK7,sK8,sK9,sK5),sK8) = iProver_top
% 2.18/1.02      | v1_xboole_0(sK8) = iProver_top ),
% 2.18/1.02      inference(superposition,[status(thm)],[c_5132,c_1173]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_18,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 2.18/1.02      | m1_subset_1(sK2(X1,X2,X3,X4,X0),X2)
% 2.18/1.02      | k1_xboole_0 = X4
% 2.18/1.02      | k1_xboole_0 = X3
% 2.18/1.02      | k1_xboole_0 = X2
% 2.18/1.02      | k1_xboole_0 = X1 ),
% 2.18/1.02      inference(cnf_transformation,[],[f68]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1169,plain,
% 2.18/1.02      ( k1_xboole_0 = X0
% 2.18/1.02      | k1_xboole_0 = X1
% 2.18/1.02      | k1_xboole_0 = X2
% 2.18/1.02      | k1_xboole_0 = X3
% 2.18/1.02      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X0),X3)) != iProver_top
% 2.18/1.02      | m1_subset_1(sK2(X2,X1,X0,X3,X4),X1) = iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_2406,plain,
% 2.18/1.02      ( sK6 = k1_xboole_0
% 2.18/1.02      | sK7 = k1_xboole_0
% 2.18/1.02      | sK8 = k1_xboole_0
% 2.18/1.02      | sK9 = k1_xboole_0
% 2.18/1.02      | m1_subset_1(sK2(sK6,sK7,sK8,sK9,sK5),sK7) = iProver_top ),
% 2.18/1.02      inference(superposition,[status(thm)],[c_1412,c_1169]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_3054,plain,
% 2.18/1.02      ( m1_subset_1(sK2(sK6,sK7,sK8,sK9,sK5),sK7) = iProver_top ),
% 2.18/1.02      inference(global_propositional_subsumption,
% 2.18/1.02                [status(thm)],
% 2.18/1.02                [c_2406,c_21,c_55,c_58,c_71,c_74,c_1361,c_1403,c_1406,
% 2.18/1.02                 c_1483,c_1486,c_1503,c_1726,c_1749,c_1752,c_2366,c_2381]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_3059,plain,
% 2.18/1.02      ( r2_hidden(sK2(sK6,sK7,sK8,sK9,sK5),sK7) = iProver_top
% 2.18/1.02      | v1_xboole_0(sK7) = iProver_top ),
% 2.18/1.02      inference(superposition,[status(thm)],[c_3054,c_1173]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_19,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 2.18/1.02      | m1_subset_1(sK1(X1,X2,X3,X4,X0),X1)
% 2.18/1.02      | k1_xboole_0 = X4
% 2.18/1.02      | k1_xboole_0 = X3
% 2.18/1.02      | k1_xboole_0 = X2
% 2.18/1.02      | k1_xboole_0 = X1 ),
% 2.18/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1168,plain,
% 2.18/1.02      ( k1_xboole_0 = X0
% 2.18/1.02      | k1_xboole_0 = X1
% 2.18/1.02      | k1_xboole_0 = X2
% 2.18/1.02      | k1_xboole_0 = X3
% 2.18/1.02      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X1),X0),X3)) != iProver_top
% 2.18/1.02      | m1_subset_1(sK1(X2,X1,X0,X3,X4),X2) = iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1661,plain,
% 2.18/1.02      ( sK6 = k1_xboole_0
% 2.18/1.02      | sK7 = k1_xboole_0
% 2.18/1.02      | sK8 = k1_xboole_0
% 2.18/1.02      | sK9 = k1_xboole_0
% 2.18/1.02      | m1_subset_1(sK1(sK6,sK7,sK8,sK9,sK5),sK6) = iProver_top ),
% 2.18/1.02      inference(superposition,[status(thm)],[c_1412,c_1168]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_2088,plain,
% 2.18/1.02      ( sK6 = k1_xboole_0
% 2.18/1.02      | sK7 = k1_xboole_0
% 2.18/1.02      | m1_subset_1(sK1(sK6,sK7,sK8,sK9,sK5),sK6) = iProver_top ),
% 2.18/1.02      inference(global_propositional_subsumption,
% 2.18/1.02                [status(thm)],
% 2.18/1.02                [c_1661,c_21,c_55,c_58,c_71,c_74,c_1361,c_1403,c_1406,
% 2.18/1.02                 c_1486,c_1503,c_1726]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_2768,plain,
% 2.18/1.02      ( sK6 = k1_xboole_0
% 2.18/1.02      | sK7 = k1_xboole_0
% 2.18/1.02      | r2_hidden(sK1(sK6,sK7,sK8,sK9,sK5),sK6) = iProver_top
% 2.18/1.02      | v1_xboole_0(sK6) = iProver_top ),
% 2.18/1.02      inference(superposition,[status(thm)],[c_2088,c_1173]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1753,plain,
% 2.18/1.02      ( v1_xboole_0(k2_zfmisc_1(sK6,sK7)) = iProver_top
% 2.18/1.02      | v1_xboole_0(sK7) != iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_1752]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1750,plain,
% 2.18/1.02      ( v1_xboole_0(k2_zfmisc_1(sK6,sK7)) = iProver_top
% 2.18/1.02      | v1_xboole_0(sK6) != iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_1749]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1487,plain,
% 2.18/1.02      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top
% 2.18/1.02      | v1_xboole_0(sK8) != iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_1486]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1484,plain,
% 2.18/1.02      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top
% 2.18/1.02      | v1_xboole_0(k2_zfmisc_1(sK6,sK7)) != iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_1483]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1407,plain,
% 2.18/1.02      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9)) = iProver_top
% 2.18/1.02      | v1_xboole_0(sK9) != iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_1406]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1404,plain,
% 2.18/1.02      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9)) = iProver_top
% 2.18/1.02      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) != iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_1403]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1362,plain,
% 2.18/1.02      ( r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9)) != iProver_top
% 2.18/1.02      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9)) != iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_1361]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_22,plain,
% 2.18/1.02      ( r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9)) = iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(contradiction,plain,
% 2.18/1.02      ( $false ),
% 2.18/1.02      inference(minisat,
% 2.18/1.02                [status(thm)],
% 2.18/1.02                [c_5388,c_5381,c_5137,c_3059,c_2768,c_2381,c_2366,c_1753,
% 2.18/1.02                 c_1752,c_1750,c_1749,c_1487,c_1484,c_1483,c_1407,c_1404,
% 2.18/1.02                 c_1403,c_1362,c_1361,c_74,c_71,c_58,c_55,c_22,c_21]) ).
% 2.18/1.02  
% 2.18/1.02  
% 2.18/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.18/1.02  
% 2.18/1.02  ------                               Statistics
% 2.18/1.02  
% 2.18/1.02  ------ General
% 2.18/1.02  
% 2.18/1.02  abstr_ref_over_cycles:                  0
% 2.18/1.02  abstr_ref_under_cycles:                 0
% 2.18/1.02  gc_basic_clause_elim:                   0
% 2.18/1.02  forced_gc_time:                         0
% 2.18/1.02  parsing_time:                           0.011
% 2.18/1.02  unif_index_cands_time:                  0.
% 2.18/1.02  unif_index_add_time:                    0.
% 2.18/1.02  orderings_time:                         0.
% 2.18/1.02  out_proof_time:                         0.01
% 2.18/1.02  total_time:                             0.19
% 2.18/1.02  num_of_symbols:                         50
% 2.18/1.02  num_of_terms:                           7658
% 2.18/1.02  
% 2.18/1.02  ------ Preprocessing
% 2.18/1.02  
% 2.18/1.02  num_of_splits:                          0
% 2.18/1.02  num_of_split_atoms:                     0
% 2.18/1.02  num_of_reused_defs:                     0
% 2.18/1.02  num_eq_ax_congr_red:                    84
% 2.18/1.02  num_of_sem_filtered_clauses:            1
% 2.18/1.02  num_of_subtypes:                        0
% 2.18/1.02  monotx_restored_types:                  0
% 2.18/1.02  sat_num_of_epr_types:                   0
% 2.18/1.02  sat_num_of_non_cyclic_types:            0
% 2.18/1.02  sat_guarded_non_collapsed_types:        0
% 2.18/1.02  num_pure_diseq_elim:                    0
% 2.18/1.02  simp_replaced_by:                       0
% 2.18/1.02  res_preprocessed:                       99
% 2.18/1.02  prep_upred:                             0
% 2.18/1.02  prep_unflattend:                        12
% 2.18/1.02  smt_new_axioms:                         0
% 2.18/1.02  pred_elim_cands:                        5
% 2.18/1.02  pred_elim:                              0
% 2.18/1.02  pred_elim_cl:                           0
% 2.18/1.02  pred_elim_cycles:                       2
% 2.18/1.02  merged_defs:                            8
% 2.18/1.02  merged_defs_ncl:                        0
% 2.18/1.02  bin_hyper_res:                          8
% 2.18/1.02  prep_cycles:                            4
% 2.18/1.02  pred_elim_time:                         0.003
% 2.18/1.02  splitting_time:                         0.
% 2.18/1.02  sem_filter_time:                        0.
% 2.18/1.02  monotx_time:                            0.
% 2.18/1.02  subtype_inf_time:                       0.
% 2.18/1.02  
% 2.18/1.02  ------ Problem properties
% 2.18/1.02  
% 2.18/1.02  clauses:                                21
% 2.18/1.02  conjectures:                            2
% 2.18/1.02  epr:                                    7
% 2.18/1.02  horn:                                   13
% 2.18/1.02  ground:                                 1
% 2.18/1.02  unary:                                  3
% 2.18/1.02  binary:                                 8
% 2.18/1.02  lits:                                   66
% 2.18/1.02  lits_eq:                                26
% 2.18/1.02  fd_pure:                                0
% 2.18/1.02  fd_pseudo:                              0
% 2.18/1.02  fd_cond:                                4
% 2.18/1.02  fd_pseudo_cond:                         1
% 2.18/1.02  ac_symbols:                             0
% 2.18/1.02  
% 2.18/1.02  ------ Propositional Solver
% 2.18/1.02  
% 2.18/1.02  prop_solver_calls:                      29
% 2.18/1.02  prop_fast_solver_calls:                 783
% 2.18/1.02  smt_solver_calls:                       0
% 2.18/1.02  smt_fast_solver_calls:                  0
% 2.18/1.02  prop_num_of_clauses:                    1599
% 2.18/1.02  prop_preprocess_simplified:             6733
% 2.18/1.02  prop_fo_subsumed:                       22
% 2.18/1.02  prop_solver_time:                       0.
% 2.18/1.02  smt_solver_time:                        0.
% 2.18/1.02  smt_fast_solver_time:                   0.
% 2.18/1.02  prop_fast_solver_time:                  0.
% 2.18/1.02  prop_unsat_core_time:                   0.
% 2.18/1.02  
% 2.18/1.02  ------ QBF
% 2.18/1.02  
% 2.18/1.02  qbf_q_res:                              0
% 2.18/1.02  qbf_num_tautologies:                    0
% 2.18/1.02  qbf_prep_cycles:                        0
% 2.18/1.02  
% 2.18/1.02  ------ BMC1
% 2.18/1.02  
% 2.18/1.02  bmc1_current_bound:                     -1
% 2.18/1.02  bmc1_last_solved_bound:                 -1
% 2.18/1.02  bmc1_unsat_core_size:                   -1
% 2.18/1.02  bmc1_unsat_core_parents_size:           -1
% 2.18/1.02  bmc1_merge_next_fun:                    0
% 2.18/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.18/1.02  
% 2.18/1.02  ------ Instantiation
% 2.18/1.02  
% 2.18/1.02  inst_num_of_clauses:                    596
% 2.18/1.02  inst_num_in_passive:                    316
% 2.18/1.02  inst_num_in_active:                     205
% 2.18/1.02  inst_num_in_unprocessed:                75
% 2.18/1.02  inst_num_of_loops:                      210
% 2.18/1.02  inst_num_of_learning_restarts:          0
% 2.18/1.02  inst_num_moves_active_passive:          1
% 2.18/1.02  inst_lit_activity:                      0
% 2.18/1.02  inst_lit_activity_moves:                0
% 2.18/1.02  inst_num_tautologies:                   0
% 2.18/1.02  inst_num_prop_implied:                  0
% 2.18/1.02  inst_num_existing_simplified:           0
% 2.18/1.02  inst_num_eq_res_simplified:             0
% 2.18/1.02  inst_num_child_elim:                    0
% 2.18/1.02  inst_num_of_dismatching_blockings:      35
% 2.18/1.02  inst_num_of_non_proper_insts:           413
% 2.18/1.02  inst_num_of_duplicates:                 0
% 2.18/1.02  inst_inst_num_from_inst_to_res:         0
% 2.18/1.02  inst_dismatching_checking_time:         0.
% 2.18/1.02  
% 2.18/1.02  ------ Resolution
% 2.18/1.02  
% 2.18/1.02  res_num_of_clauses:                     0
% 2.18/1.02  res_num_in_passive:                     0
% 2.18/1.02  res_num_in_active:                      0
% 2.18/1.02  res_num_of_loops:                       103
% 2.18/1.02  res_forward_subset_subsumed:            20
% 2.18/1.02  res_backward_subset_subsumed:           0
% 2.18/1.02  res_forward_subsumed:                   0
% 2.18/1.02  res_backward_subsumed:                  0
% 2.18/1.02  res_forward_subsumption_resolution:     0
% 2.18/1.02  res_backward_subsumption_resolution:    0
% 2.18/1.02  res_clause_to_clause_subsumption:       97
% 2.18/1.02  res_orphan_elimination:                 0
% 2.18/1.02  res_tautology_del:                      37
% 2.18/1.02  res_num_eq_res_simplified:              0
% 2.18/1.02  res_num_sel_changes:                    0
% 2.18/1.02  res_moves_from_active_to_pass:          0
% 2.18/1.02  
% 2.18/1.02  ------ Superposition
% 2.18/1.02  
% 2.18/1.02  sup_time_total:                         0.
% 2.18/1.02  sup_time_generating:                    0.
% 2.18/1.02  sup_time_sim_full:                      0.
% 2.18/1.02  sup_time_sim_immed:                     0.
% 2.18/1.02  
% 2.18/1.02  sup_num_of_clauses:                     57
% 2.18/1.02  sup_num_in_active:                      42
% 2.18/1.02  sup_num_in_passive:                     15
% 2.18/1.02  sup_num_of_loops:                       41
% 2.18/1.02  sup_fw_superposition:                   25
% 2.18/1.02  sup_bw_superposition:                   18
% 2.18/1.02  sup_immediate_simplified:               5
% 2.18/1.02  sup_given_eliminated:                   0
% 2.18/1.02  comparisons_done:                       0
% 2.18/1.02  comparisons_avoided:                    4
% 2.18/1.02  
% 2.18/1.02  ------ Simplifications
% 2.18/1.02  
% 2.18/1.02  
% 2.18/1.02  sim_fw_subset_subsumed:                 3
% 2.18/1.02  sim_bw_subset_subsumed:                 0
% 2.18/1.02  sim_fw_subsumed:                        2
% 2.18/1.02  sim_bw_subsumed:                        0
% 2.18/1.02  sim_fw_subsumption_res:                 0
% 2.18/1.02  sim_bw_subsumption_res:                 0
% 2.18/1.02  sim_tautology_del:                      0
% 2.18/1.02  sim_eq_tautology_del:                   1
% 2.18/1.02  sim_eq_res_simp:                        0
% 2.18/1.02  sim_fw_demodulated:                     0
% 2.18/1.02  sim_bw_demodulated:                     0
% 2.18/1.02  sim_light_normalised:                   0
% 2.18/1.02  sim_joinable_taut:                      0
% 2.18/1.02  sim_joinable_simp:                      0
% 2.18/1.02  sim_ac_normalised:                      0
% 2.18/1.02  sim_smt_subsumption:                    0
% 2.18/1.02  
%------------------------------------------------------------------------------
